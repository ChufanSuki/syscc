// This file contains a recursive descent parser for C.
//
// Most functions in this file are named after the symbols they are
// supposed to read from an input token list. For example, stmt() is
// responsible for reading a statement from a token list. The function
// then construct an AST node representing a statement.
//
// Each function conceptually returns two values, an AST node and
// remaining part of the input tokens. Since C doesn't support
// multiple return values, the remaining tokens are returned to the
// caller via a pointer argument.
//
// Input tokens are represented by a linked list. Unlike many recursive
// descent parsers, we don't have the notion of the "input token stream".
// Most parsing functions don't change the global state of the parser.
// So it is very easy to lookahead arbitrary number of tokens in this
// parser.

#include <list>
#include "syscc.hpp"
// All local variable instances created during parsing are
// accumulated to this list.
static Obj *locals;
static Obj *globals;

static Type *declspec(Token **rest, Token *tok);
static Type *declarator(Token **rest, Token *tok, Type *ty);
static Node *declaration(Token **rest, Token *tok);
static Node *compound_stmt(Token **rest, Token *tok);
static Node *stmt(Token **rest, Token *tok);
static Node *expr_stmt(Token **rest, Token *tok);
static Node *expr(Token **rest, Token *tok);
static Node *assign(Token **rest, Token *tok);
static Node *equality(Token **rest, Token *tok);
static Node *relational(Token **rest, Token *tok);
static Node *add(Token **rest, Token *tok);
static Node *mul(Token **rest, Token *tok);
static Node *postfix(Token **rest, Token *tok);
static Node *unary(Token **rest, Token *tok);
static Node *primary(Token **rest, Token *tok);

// Find a local variable by name.
static Obj *find_var(Token *tok) {
  for (Obj *var = locals; var; var = var->next)
    if (strlen(var->name) == tok->len && !strncmp(tok->loc, var->name, tok->len)) return var;
  for (Obj *var = globals; var; var = var->next)
    if (strlen(var->name) == tok->len && !strncmp(tok->loc, var->name, tok->len)) return var;
  return NULL;
}

static Node *new_node(NodeKind kind, Token *tok) {
  Node *node = (Node *)calloc(1, sizeof(Node));
  node->kind = kind;
  node->tok = tok;
  return node;
}

static Node *new_binary(NodeKind kind, Node *lhs, Node *rhs, Token *tok) {
  Node *node = new_node(kind, tok);
  node->lhs = lhs;
  node->rhs = rhs;
  return node;
}

static Node *new_unary(NodeKind kind, Node *expr, Token *tok) {
  Node *node = new_node(kind, tok);
  node->lhs = expr;
  return node;
}

static Node *new_num(int val, Token *tok) {
  Node *node = new_node(ND_NUM, tok);
  node->val = val;
  return node;
}

static Node *new_var_node(Obj *var, Token *tok) {
  Node *node = new_node(ND_VAR, tok);
  node->var = var;
  return node;
}

static Obj *new_var(char *name, Type *ty) {
  Obj *var = (Obj *)calloc(1, sizeof(Obj));
  var->name = name;
  var->ty = ty;
  return var;
}

static Obj *new_lvar(char *name, Type *ty) {
  Obj *var = new_var(name, ty);
  var->is_local = true;
  var->next = locals;
  locals = var;
  return var;
}

static Obj *new_gvar(char *name, Type *ty) {
  Obj *var = new_var(name, ty);
  var->next = globals;
  globals = var;
  return var;
}

static char *new_unique_name(void) {
  static int id = 0;
  char *buf = (char*)calloc(1, 20);
  sprintf(buf, ".L..%d", id++);
  return buf;
}

static Obj *new_anon_gvar(Type *ty) { return new_gvar(new_unique_name(), ty); }

static Obj *new_string_literal(char *p, Type *ty) {
  Obj *var = new_anon_gvar(ty);
  var->init_data = p;
  return var;
}

static char *get_ident(Token *tok) {
  if (tok->kind != TK_IDENT) error_tok(tok, "expected an identifier");
  return strndup(tok->loc, tok->len);
}

static int get_number(Token *tok) {
  if (tok->kind != TK_NUM) error_tok(tok, "expected a number");
  return tok->val;
}

// declspec = "char" | "int"
static Type *declspec(Token **rest, Token *tok) {
  if (equal(tok, "char")) {
    *rest = tok->next;
    return ty_char;
  }

  *rest = skip(tok, "int");
  return ty_int;
}

// func-params = (param ("," param)*)? ")"
// param       = declspec declarator
static Type *func_params(Token **rest, Token *tok, Type *ty) {
  Type head = {};
  Type *cur = &head;

  while (!equal(tok, ")")) {
    if (cur != &head) tok = skip(tok, ",");
    Type *basety = declspec(&tok, tok);
    Type *ty = declarator(&tok, tok, basety);
    cur = cur->next = copy_type(ty);
  }

  ty = func_type(ty);
  ty->params = head.next;
  *rest = tok->next;
  return ty;
}

// type-suffix = "(" func-params
//             | "[" num "]" type-suffix
//             | ε
static Type *type_suffix(Token **rest, Token *tok, Type *ty) {
  if (equal(tok, "(")) return func_params(rest, tok->next, ty);

  if (equal(tok, "[")) {
    int sz = get_number(tok->next);
    tok = skip(tok->next->next, "]");
    ty = type_suffix(rest, tok, ty);
    return array_of(ty, sz);
  }

  *rest = tok;
  return ty;
}

// declarator = "*"* ident type-suffix
static Type *declarator(Token **rest, Token *tok, Type *ty) {
  while (consume(&tok, tok, "*")) ty = pointer_to(ty);

  if (tok->kind != TK_IDENT) error_tok(tok, "expected a variable name");

  ty = type_suffix(rest, tok->next, ty);
  ty->name = tok;
  return ty;
}

// FIXME: "int;" passed parsing
// declaration = declspec (declarator ("=" expr)? ("," declarator ("=" expr)?)*)? ";"
static Node *declaration(Token **rest, Token *tok) {
  Type *basety = declspec(&tok, tok);

  Node head = {};
  Node *cur = &head;
  int i = 0;

  while (!equal(tok, ";")) {
    if (i++ > 0) tok = skip(tok, ",");

    Type *ty = declarator(&tok, tok, basety);
    if (find_var(ty->name)) {
      char message[50];
      sprintf(message, "redefinition of '%s'", get_ident(ty->name));
      error_tok(tok, message);
    }
    Obj *var = new_lvar(get_ident(ty->name), ty);

    if (!equal(tok, "=")) continue;

    Node *lhs = new_var_node(var, ty->name);
    Node *rhs = assign(&tok, tok->next);
    Node *node = new_binary(ND_ASSIGN, lhs, rhs, tok);
    cur = cur->next = new_unary(ND_EXPR_STMT, node, tok);
  }

  Node *node = new_node(ND_BLOCK, tok);
  node->body = head.next;
  *rest = tok->next;
  return node;
}

// Returns true if a given token represents a type.
static bool is_typename(Token *tok) { return equal(tok, "char") || equal(tok, "int"); }

// stmt = "return" expr ";"
//      | "if" "(" expr ")" stmt ("else" stmt)?
//      | "for" "(" expr-stmt expr? ";" expr? ")" stmt
//      | "while" "(" expr ")" stmt
//      | "{" compound-stmt
//      | expr-stmt
static Node *stmt(Token **rest, Token *tok) {
  if (equal(tok, "return")) {
    Node *node = new_node(ND_RETURN, tok);
    node->lhs = expr(&tok, tok->next);
    *rest = skip(tok, ";");
    return node;
  }
  if (equal(tok, "for")) {
    Node *node = new_node(ND_FOR, tok);
    tok = skip(tok->next, "(");

    node->init = expr_stmt(&tok, tok);

    if (!equal(tok, ";")) node->cond = expr(&tok, tok);
    tok = skip(tok, ";");

    if (!equal(tok, ")")) node->inc = expr(&tok, tok);
    tok = skip(tok, ")");

    node->then = stmt(rest, tok);
    return node;
  }

  if (equal(tok, "while")) {
    Node *node = new_node(ND_FOR, tok);
    tok = skip(tok->next, "(");
    node->cond = expr(&tok, tok);
    tok = skip(tok, ")");
    node->then = stmt(rest, tok);
    return node;
  }

  if (equal(tok, "{")) return compound_stmt(rest, tok->next);

  if (equal(tok, "if")) {
    Node *node = new_node(ND_IF, tok);
    tok = skip(tok->next, "(");
    node->cond = expr(&tok, tok);
    tok = skip(tok, ")");
    node->then = stmt(&tok, tok);
    if (equal(tok, "else")) node->els = stmt(&tok, tok->next);
    *rest = tok;
    return node;
  }

  return expr_stmt(rest, tok);
}

// compound-stmt = (declaration | stmt)* "}"
static Node *compound_stmt(Token **rest, Token *tok) {
  Node head = {};
  Node *cur = &head;
  while (!equal(tok, "}")) {
    if (is_typename(tok))
      cur = cur->next = declaration(&tok, tok);
    else
      cur = cur->next = stmt(&tok, tok);
    add_type(cur);
  }

  Node *node = new_node(ND_BLOCK, tok);
  node->body = head.next;
  *rest = tok->next;
  return node;
}

// expr-stmt = expr ";"
static Node *expr_stmt(Token **rest, Token *tok) {
  if (equal(tok, ";")) {
    *rest = tok->next;
    return new_node(ND_BLOCK, tok);
  }
  Node *node = new_node(ND_EXPR_STMT, tok);
  node->lhs = expr(&tok, tok);
  *rest = skip(tok, ";");
  return node;
}

// expr = assign
static Node *expr(Token **rest, Token *tok) { return assign(rest, tok); }

// assign = equality ("=" assign)?
static Node *assign(Token **rest, Token *tok) {
  Node *node = equality(&tok, tok);

  if (equal(tok, "=")) node = new_binary(ND_ASSIGN, node, assign(&tok, tok->next), tok);
  *rest = tok;
  return node;
}

// equality = relational ("==" relational | "!=" relational)*
static Node *equality(Token **rest, Token *tok) {
  Node *node = relational(&tok, tok);
  for (;;) {
    Token *start = tok;
    if (equal(tok, "==")) {
      node = new_binary(ND_EQ, node, relational(&tok, tok->next), start);
      continue;
    }

    if (equal(tok, "!=")) {
      node = new_binary(ND_NE, node, relational(&tok, tok->next), start);
      continue;
    }

    *rest = tok;
    return node;
  }
}

// relational = add ("<" add | "<=" add | ">" add | ">=" add)*
static Node *relational(Token **rest, Token *tok) {
  Node *node = add(&tok, tok);

  for (;;) {
    Token *start = tok;

    if (equal(tok, "<")) {
      node = new_binary(ND_LT, node, add(&tok, tok->next), start);
      continue;
    }

    if (equal(tok, "<=")) {
      node = new_binary(ND_LE, node, add(&tok, tok->next), start);
      continue;
    }

    if (equal(tok, ">")) {
      node = new_binary(ND_LT, add(&tok, tok->next), node, start);
      continue;
    }

    if (equal(tok, ">=")) {
      node = new_binary(ND_LE, add(&tok, tok->next), node, start);
      continue;
    }

    *rest = tok;
    return node;
  }
}

// In C, `+` operator is overloaded to perform the pointer arithmetic.
// If p is a pointer, p+n adds not n but sizeof(*p)*n to the value of p,
// so that p+n points to the location n elements (not bytes) ahead of p.
// In other words, we need to scale an integer value before adding to a
// pointer value. This function takes care of the scaling.
static Node *new_add(Node *lhs, Node *rhs, Token *tok) {
  add_type(lhs);
  add_type(rhs);

  // num + num
  if (is_integer(lhs->ty) && is_integer(rhs->ty)) return new_binary(ND_ADD, lhs, rhs, tok);

  // error: ptr + ptr
  if (lhs->ty->base && rhs->ty->base) error_tok(tok, "invalid operands");

  // Canonicalize `num + ptr` to `ptr + num`.
  if (!lhs->ty->base && rhs->ty->base) {
    Node *tmp = lhs;
    lhs = rhs;
    rhs = tmp;
  }

  // ptr + num
  rhs = new_binary(ND_MUL, rhs, new_num(lhs->ty->base->size, tok), tok);
  return new_binary(ND_ADD, lhs, rhs, tok);
}

// Like `+`, `-` is overloaded for the pointer type.
static Node *new_sub(Node *lhs, Node *rhs, Token *tok) {
  add_type(lhs);
  add_type(rhs);

  // num - num
  if (is_integer(lhs->ty) && is_integer(rhs->ty)) return new_binary(ND_SUB, lhs, rhs, tok);

  // ptr - num
  if (lhs->ty->base && is_integer(rhs->ty)) {
    rhs = new_binary(ND_MUL, rhs, new_num(lhs->ty->base->size, tok), tok);
    add_type(rhs);
    Node *node = new_binary(ND_SUB, lhs, rhs, tok);
    node->ty = lhs->ty;
    return node;
  }

  // ptr - ptr, which returns how many elements are between the two.
  if (lhs->ty->base && rhs->ty->base) {
    Node *node = new_binary(ND_SUB, lhs, rhs, tok);
    node->ty = ty_int;
    return new_binary(ND_DIV, node, new_num(lhs->ty->base->size, tok), tok);
  }

  error_tok(tok, "invalid operands");
}

// add = mul ("+" mul | "-" mul)*
static Node *add(Token **rest, Token *tok) {
  Node *node = mul(&tok, tok);
  for (;;) {
    Token *start = tok;

    if (equal(tok, "+")) {
      node = new_add(node, mul(&tok, tok->next), start);
      continue;
    }

    if (equal(tok, "-")) {
      node = new_sub(node, mul(&tok, tok->next), start);
      continue;
    }

    *rest = tok;
    return node;
  }
}

// mul = unary ("*" unary | "/" unary)*
static Node *mul(Token **rest, Token *tok) {
  Node *node = unary(&tok, tok);

  for (;;) {
    Token *start = tok;

    if (equal(tok, "*")) {
      node = new_binary(ND_MUL, node, unary(&tok, tok->next), start);
      continue;
    }

    if (equal(tok, "/")) {
      node = new_binary(ND_DIV, node, unary(&tok, tok->next), start);
      continue;
    }

    *rest = tok;
    return node;
  }
}

// unary = ("+" | "-" | "*" | "&") unary
//       | postfix
static Node *unary(Token **rest, Token *tok) {
  if (equal(tok, "+")) return unary(rest, tok->next);

  if (equal(tok, "-")) return new_unary(ND_NEG, unary(rest, tok->next), tok);

  if (equal(tok, "&")) return new_unary(ND_ADDR, unary(rest, tok->next), tok);

  if (equal(tok, "*")) return new_unary(ND_DEREF, unary(rest, tok->next), tok);

  return postfix(rest, tok);
}

// postfix = primary ("[" expr "]")*
static Node *postfix(Token **rest, Token *tok) {
  Node *node = primary(&tok, tok);

  while (equal(tok, "[")) {
    // x[y] is short for *(x+y)
    Token *start = tok;
    Node *idx = expr(&tok, tok->next);
    tok = skip(tok, "]");
    node = new_unary(ND_DEREF, new_add(node, idx, start), start);
  }
  *rest = tok;
  return node;
}

// funcall = ident "(" (assign ("," assign)*)? ")"
static Node *funcall(Token **rest, Token *tok) {
  Token *start = tok;
  tok = tok->next->next;

  Node head = {};
  Node *cur = &head;

  while (!equal(tok, ")")) {
    if (cur != &head) tok = skip(tok, ",");
    cur = cur->next = assign(&tok, tok);
  }

  *rest = skip(tok, ")");

  Node *node = new_node(ND_FUNCALL, start);
  node->funcname = strndup(start->loc, start->len);
  node->args = head.next;
  return node;
}

// primary = "(" expr ")" | "sizeof" unary | num | str | ident func-args?
static Node *primary(Token **rest, Token *tok) {
  if (equal(tok, "(")) {
    Node *node = expr(&tok, tok->next);
    *rest = skip(tok, ")");
    return node;
  }

  if (equal(tok, "sizeof")) {
    Node *node = unary(rest, tok->next);
    add_type(node);
    return new_num(node->ty->size, tok);
  }

  if (tok->kind == TK_NUM) {
    Node *node = new_num(tok->val, tok);
    *rest = tok->next;
    return node;
  }

  if (tok->kind == TK_STR) {
    Obj *var = new_string_literal(tok->str, tok->ty);
    *rest = tok->next;
    return new_var_node(var, tok);
  }

  if (tok->kind == TK_IDENT) {
    // Function call
    if (equal(tok->next, "(")) return funcall(rest, tok);

    // Variable
    Obj *var = find_var(tok);
    if (!var) error_tok(tok, "undefined variable");
    *rest = tok->next;
    return new_var_node(var, tok);
  }

  error_tok(tok, "expected an expression");
}

static void create_param_lvars(Type *param) {
  if (param) {
    create_param_lvars(param->next);
    new_lvar(get_ident(param->name), param);
  }
}

// function-definition = declspec declarator "{" compound-stmt
static Token *function(Token *tok, Type *basety) {
  Type *ty = declarator(&tok, tok, basety);

  Obj *fn = new_gvar(get_ident(ty->name), ty);
  fn->is_function = true;

  locals = NULL;
  create_param_lvars(ty->params);
  fn->params = locals;

  tok = skip(tok, "{");
  fn->body = compound_stmt(&tok, tok);
  fn->locals = locals;
  return tok;
}

static Token *global_variable(Token *tok, Type *basety) {
  bool first = true;

  while (!consume(&tok, tok, ";")) {
    if (!first) tok = skip(tok, ",");
    first = false;

    Type *ty = declarator(&tok, tok, basety);
    new_gvar(get_ident(ty->name), ty);
  }
  return tok;
}

// Lookahead tokens and returns true if a given token is a start
// of a function definition or declaration.
static bool is_function(Token *tok) {
  if (equal(tok, ";")) return false;

  Type dummy = {};
  Type *ty = declarator(&tok, tok, &dummy);
  return ty->kind == TY_FUNC;
}

// program = (function-definition | global-variable)*
Obj *parse(Token *tok) {
  globals = NULL;

  while (tok->kind != TK_EOF) {
    Type *basety = declspec(&tok, tok);

    // Function
    if (is_function(tok)) {
      tok = function(tok, basety);
      continue;
    }

    // Global variable
    tok = global_variable(tok, basety);
  }
  return globals;
}

// print ast

static int ncount = 1;

static void gen_expr(Node *node, int father) {
  switch (node->kind) {
    case ND_NUM:
      printf("  node%d [label=\"%d\"];\n", ncount++, node->val);
      printf("  node%d -> node%d;\n", father, ncount - 1);
      return;
    case ND_NEG:
      printf("  node%d [label=\"%s\"];\n", ncount++, "NEG");
      printf("  node%d -> node%d;\n", father, ncount - 1);
      gen_expr(node->lhs, ncount - 1);
      return;
    case ND_VAR:
      printf("  node%d [label=\"%s\"];\n", ncount++, "VAR");
      printf("  node%d -> node%d;\n", father, ncount - 1);
      // gen_addr(node);
      return;
    case ND_DEREF:
      printf("  node%d [label=\"%s\"];\n", ncount++, "DEREF");
      printf("  node%d -> node%d;\n", father, ncount - 1);
      gen_expr(node->lhs, ncount - 1);
      return;
    case ND_ADDR:
      printf("  node%d [label=\"%s\"];\n", ncount++, "ADDR");
      printf("  node%d -> node%d;\n", father, ncount - 1);
      // gen_addr(node->lhs);
      return;
    case ND_ASSIGN:
      printf("  node%d [label=\"%s\"];\n", ncount++, "ASSIGN");
      printf("  node%d -> node%d;\n", father, ncount - 1);
      // gen_addr(node->lhs, ncount);
      gen_expr(node->rhs, ncount - 1);
      return;
    case ND_FUNCALL:
      printf("  node%d [label=\"%s\"];\n", ncount++, "FUNCALL");
      printf("  node%d -> node%d;\n", father, ncount - 1);
      int nargs = 0;
      for (Node *arg = node->args; arg; arg = arg->next) {
        gen_expr(arg, ncount - 1);
        nargs++;
      }
      return;
  }

  switch (node->kind) {
    case ND_ADD:
      printf("  node%d [label=\"%s\"]\n", ncount++, "ADD");
      printf("  node%d -> node%d\n", father, ncount - 1);
      break;
    case ND_SUB:
      printf("  node%d [label=\"%s\"]\n", ncount++, "SUB");
      printf("  node%d -> node%d\n", father, ncount - 1);
      break;
    case ND_MUL:
      printf("  node%d [label=\"%s\"]\n", ncount++, "MUL");
      printf("  node%d -> node%d\n", father, ncount - 1);
      break;
    case ND_DIV:
      printf("  node%d [label=\"%s\"]\n", ncount++, "DIV");
      printf("  node%d -> node%d\n", father, ncount - 1);
      break;
    case ND_EQ:
      printf("  node%d [label=\"%s\"]\n", ncount++, "EQ");
      printf("  node%d -> node%d\n", father, ncount - 1);
      break;
    case ND_NE:
      printf("  node%d [label=\"%s\"]\n", ncount++, "NE");
      printf("  node%d -> node%d\n", father, ncount - 1);
      break;
    case ND_LT:
      printf("  node%d [label=\"%s\"]\n", ncount++, "LT");
      printf("  node%d -> node%d\n", father, ncount - 1);
      break;
    case ND_LE:
      printf("  node%d [label=\"%s\"]\n", ncount++, "LE");
      printf("  node%d -> node%d\n", father, ncount - 1);
      break;
  }
  int tmp = ncount;
  gen_expr(node->rhs, ncount - 1);
  gen_expr(node->lhs, tmp - 1);
}

static void gen_stmt(Node *node, int father) {
  switch (node->kind) {
    case ND_IF: {
      printf("  node%d [label=\"%s\"]\n", ncount++, "IF");
      printf("  node%d -> node%d\n", father, ncount - 1);
      gen_stmt(node->then, ncount);
      if (node->els) gen_stmt(node->els, ncount);
      return;
    }
    case ND_FOR: {
      if (node->init) {
        printf("  node%d [label=\"%s\"]\n", ncount++, "FOR");
        printf("  node%d -> node%d\n", father, ncount - 1);
      } else {
        printf("  node%d [label=\"%s\"]\n", ncount++, "WHILE");
        printf("  node%d -> node%d\n", father, ncount - 1);
      }
      if (node->init) gen_stmt(node->init, ncount);
      if (node->cond) {
        gen_expr(node->cond, ncount);
      }
      gen_stmt(node->then, ncount);
      if (node->inc) gen_expr(node->inc, ncount);
      return;
    }
    case ND_BLOCK: {
      printf("  node%d [label=\"%s\"];\n", ncount++, "BLOCK");
      printf("  node%d -> node%d;\n", father, ncount - 1);
      int tmp = ncount;
      for (Node *n = node->body; n; n = n->next) gen_stmt(n, tmp - 1);
      return;
    }
    case ND_RETURN:
      printf("  node%d [label=\"%s\"];\n", ncount++, "RETURN");
      printf("  node%d -> node%d;\n", father, ncount - 1);
      gen_expr(node->lhs, ncount - 1);
      return;
    case ND_EXPR_STMT:
      printf("  node%d [label=\"%s\"];\n", ncount++, "EXPR STMT");
      printf("  node%d -> node%d;\n", father, ncount - 1);
      gen_expr(node->lhs, ncount - 1);
      return;
  }
}
static Obj *current_fn;
static int current_fn_num;
void dotgen(Obj *prog) {
  Obj *cur = prog;
  printf(
      "digraph astgraph {\n  node [shape=none, fontsize=12, fontname=\"Courier\", height=.1];\n  ranksep=.3;\n  edge "
      "[arrowsize=.5];\n");
  printf("  node%d [label=\"%s\"];\n", ncount++, "prog");
  for (Obj *fn = prog; fn; fn = fn->next) {
    printf("  node%d [label=\"%s\"];\n", ncount++, fn->name);
    printf("  node%d -> node%d;\n", 1, ncount - 1);
    if (!fn->is_function) {
      continue;
    }
    current_fn = fn;
    current_fn_num = ncount - 1;
    gen_stmt(fn->body, current_fn_num);
  }
  printf("}\n");
}