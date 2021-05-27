#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdbool.h>
#include <string.h>
#include <list>
#include <string>

char *user_input;

//
// Tokenizer
//

typedef enum {
  TK_RESERVED, // Keywords or punctuators
  TK_NUM,      // Integer literals
  TK_EOF,      // End-of-file markers
} TokenKind;


// Token type
typedef struct Token Token;
struct Token {
  TokenKind kind; // Token kind
  Token *next;    // Next token
  int val;        // If kind is TK_NUM, its value
  char *str;      // Token string
  int len;        // Token length 
};

// Current token
Token *token;

// Reports an error and exit.
void error(char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  fprintf(stderr, "\n");
  exit(1);
}

// Reports an error location and exit.
void error_at(char *loc, char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);

  int pos = loc - user_input;
  fprintf(stderr, "%s\n", user_input);
  fprintf(stderr, "%*s", pos, ""); // print pos spaces.
  fprintf(stderr, "^ ");
  vfprintf(stderr, fmt, ap);
  fprintf(stderr, "\n");
  exit(1);
}

// Consumes the current token if it matches `op`.
bool consume(char *op) {
  if (token->kind != TK_RESERVED || token->len != strlen(op) || memcmp(token->str, op, token->len))
    return false;
  token = token->next;
  return true;
}

// Ensure that the current token is `op`.
void expect(char *op) {
  if (token->kind != TK_RESERVED || token->len != strlen(op) || memcmp(token->str, op, token->len))
    error_at(token->str, "expected \"%s\"", op);
  token = token->next;
}

// Ensure that the current token is TK_NUM.
int expect_number() {
  if (token->kind != TK_NUM)
    error_at(token->str, "expected a number");
  int val = token->val;
  token = token->next;
  return val;
}

bool at_eof() {
  return token->kind == TK_EOF;
}

// Create a new token and add it as the next token of `cur`.
Token *new_token(TokenKind kind, Token *cur, char *str, int len) {
  Token *tok = (Token*) calloc(1, sizeof(Token));
  tok->kind = kind;
  tok->str = str;
  tok->len = len;
  cur->next = tok;
  return tok;
}

bool startswith(char *p, char *q) {
  return memcmp(p, q, strlen(q)) == 0;
}

// Tokenize `p` and returns new tokens.
Token *tokenize() {
  char *p = user_input;
  Token head;
  head.next = NULL;
  Token *cur = &head;

  while (*p) {
    // Skip whitespace characters.
    if (isspace(*p)) {
      p++;
      continue;
    }

    // Multi-letter punctuator
    if (startswith(p, "==") || startswith(p, "!=") || startswith(p, "<=") || startswith(p, ">=")) {
      cur = new_token(TK_RESERVED, cur, p, 2);
      p += 2;
      continue;
    }

    // Single-letter punctuator
    if (strchr("+-*/()<>", *p)) {
      cur = new_token(TK_RESERVED, cur, p++, 1);
      continue;
    }

    // Integer literal
    if (isdigit(*p)) {
      cur = new_token(TK_NUM, cur, p, 0);
      char *q = p;
      cur->val = strtol(p, &p, 10);
      cur->len = p - q;
      continue;
    }

    error_at(p, "invalid token");
  }

  new_token(TK_EOF, cur, p, 0);
  return head.next;
}

//
// Parser
// 

typedef enum {
  ND_ADD, // +
  ND_SUB, // -
  ND_MUL, // *
  ND_DIV, // /
  ND_EQ, // == 
  ND_NE, // !=
  ND_LT, // <
  ND_LE, // <=
  ND_NUM, // Integer
} NodeKind;

// AST node  type
typedef struct Node Node;
struct Node {
	NodeKind kind; // Node kind
	Node *lhs;
	Node *rhs;
	int  val;
  char* name;
  int _num; // Used for visualize tree
  int num_num;
};

Node *new_node(NodeKind kind) {
	Node *node = (Node*) calloc(1, sizeof(Node));
	node->kind = kind;
	return node;
}

Node *new_binary(NodeKind kind, Node *lhs, Node *rhs)  {
	Node *node = new_node(kind);
	node->lhs = lhs;
	node->rhs = rhs;
  switch (kind) {
    case ND_ADD: node->name = "ND_ADD"; break;
    case ND_SUB: node->name = "ND_SUB"; break;
    case ND_DIV: node->name = "ND_DIV"; break;
    case ND_MUL: node->name = "ND_MUL"; break;
    default: node->name = "Unknown";
  }
	return node;
}

Node *new_num(int val) {
  Node *node = new_node(ND_NUM);
  node->val = val;
  node->name = "ND_NUM";
  return node;
}

Node *expr();
Node *equality();
Node *relational();
Node *add();
Node *mul();
Node *unary();
Node *primary();

// expr = equality()
Node  *expr() {
	return equality();
}

// equality = relational ("==" relational | "!=" relational)*
Node *equality() {
  Node *node = relational();

  for (;;) {
    if (consume("==")) {
      node = new_binary(ND_EQ, node, relational());
    } else if (consume("!=")) {
      node = new_binary(ND_NE, node, relational());
    } else {
      return node;
    }
  }
}

// relational = add ("<" add | "<=" add | ">" add | ">=" add)*
Node *relational() {
  Node *node = add();

  for (;;) {
    if (consume("<"))
      node = new_binary(ND_LT, node, add());
    else if (consume("<="))
      node = new_binary(ND_LE, node, add());
    else if (consume(">"))
      node = new_binary(ND_LT, add(), node);
    else if (consume(">="))
      node = new_binary(ND_LE, add(), node);
    else
      return node;
  }
}

// add = mul ("+" mul | "-" mul)*
Node *add() {
  Node *node = mul();

  for (;;) {
    if (consume("+"))
      node = new_binary(ND_ADD, node, mul());
    else if (consume("-"))
      node = new_binary(ND_SUB, node, mul());
    else
      return node;
  }
}

// mul = unary ("*" unary | "/" unary)*
Node *mul() {
  Node *node = unary();

  for (;;) {
    if (consume("*"))
      node = new_binary(ND_MUL, node, unary());
    else if (consume("/"))
      node = new_binary(ND_DIV, node, unary());
    else
      return node;
  }
}

Node *unary() {
  if (consume("+")) 
    return primary();
  else if (consume("-"))
    return new_binary(ND_SUB, new_num(0), primary());
  return primary();
}

// primary = "(" expr ")" | num
Node *primary() {
  if (consume("(")) {
    Node *node = expr();
    expect(")");
    return node;
  }

  return new_num(expect_number());
}


void bfs(Node *node) {
  int ncount = 1;
  std::list<Node*> queue;
  queue.push_back(node);
  node->_num = ncount;
  char buffer[50];
  sprintf(buffer, "  node%d [label=\"%s\"]\n", ncount, node->name);
  printf(buffer);
  ncount += 1;
  while (!queue.empty()) {
    Node *cur_node = queue.front();
    queue.pop_front();
    switch (cur_node->kind) {
    case ND_ADD: 
    case ND_SUB: 
    case ND_DIV: 
    case ND_MUL:
    {
      char buffer[50];
      sprintf(buffer, "  node%d [label=\"%s\"]\n", ncount, cur_node->lhs->name);
      printf(buffer);
      cur_node->lhs->_num = ncount;
      ncount += 1;
      char cuffer[50];
      sprintf(cuffer, "  node%d -> node%d\n", cur_node->_num, cur_node->lhs->_num);
      printf(cuffer);
      queue.push_back(cur_node->lhs);
    }
    {
      char buffer[50];
      sprintf(buffer, "  node%d [label=\"%s\"]\n", ncount, cur_node->rhs->name);
      printf(buffer);
      cur_node->rhs->_num = ncount;
      ncount += 1;
      char cuffer[50];
      sprintf(cuffer, "  node%d -> node%d\n", cur_node->_num, cur_node->rhs->_num);
      printf(cuffer);
      queue.push_back(cur_node->rhs);
    }
    break;
    case ND_NUM:
      char buffer[50];
      sprintf(buffer, "  node%d [label=\"%d\"]\n", ncount, cur_node->val);
      printf(buffer);
      cur_node->num_num = ncount;
      ncount += 1;
      char cuffer[50];
      sprintf(cuffer, "  node%d -> node%d\n", cur_node->_num, cur_node->num_num);
      printf(cuffer);
      // push leaf?
      break;
    default: printf("UNKNOWN\n");
  }

  }
}

void gendot(Node *node) {
  printf("digraph astgraph {\n  node [shape=none, fontsize=12, fontname=\"Courier\", height=.1];\n  ranksep=.3;\nedge [arrowsize=.5]\n");
  bfs(node);
}




//
// Code generator
//

void gen(Node *node) {
  if (node->kind == ND_NUM) {
    printf("  push %d\n", node->val);
    return;
  }

  gen(node->lhs);
  gen(node->rhs);

  printf("  pop rdi\n");
  printf("  pop rax\n");

  switch (node->kind) {
  case ND_ADD:
    printf("  add rax, rdi\n");
    break;
  case ND_SUB:
    printf("  sub rax, rdi\n");
    break;
  case ND_MUL:
    printf("  imul rax, rdi\n");
    break;
  case ND_DIV:
    printf("  cqo\n");
    printf("  idiv rdi\n");
    break;
  case ND_EQ:
    printf("  cmp rax, rdi\n");
    printf("  sete al\n");
    printf("  movzb rax, al\n");
    break;
  case ND_NE:
    printf("  cmp rax, rdi\n");
    printf("  setne al\n");
    printf("  movzb rax, al\n");
    break;
  case ND_LT:
    printf("  cmp rax, rdi\n");
    printf("  setl al\n");
    printf("  movzb rax, al\n");
    break;
  case ND_LE:
    printf("  cmp rax, rdi\n");
    printf("  setle al\n");
    printf("  movzb rax, al\n");
    break;
  }

  printf("  push rax\n");
}


int main(int argc, char **argv) {
  if (argc != 2) {
	  error("%s: invalid number of arguments", argv[0]);
  }
  // Tokenize and parse.
  user_input = argv[1];
  token = tokenize();
  Node *node = expr();
  gendot(node);
  //  Print out the first half of assembly.
  printf(".intel_syntax noprefix\n");
  printf(".globl main\n");
  printf("main:\n");
  // Traverse the AST to emit assembly.
  gen(node);

  // A result must be at the top of the stack, so pop it
  // to RAX to make it a program exit code.
  printf("  pop rax\n");
  printf("  ret\n");
  return 0;
}
