#include <memory>
#include "syscc.hpp"

// In C, (struct context){ 0 } is compound literal syntax that creates an instance of context with a duration of the
// enclosing scope (e.g. it exists for the duration of the function call or block in which it is created). In C++ on the
// other hand, (struct context){ 0 } creates a temporary, it exists for the duration of the full-expression, usually
// until the first ;. Note that (struct context){ 0 } is not technically C++ (GCC understands it as a compiler
// extension), context{} would be a C++ alternative, though the semantics are the same. So in C++ mode, struct context*
// ctx = &(struct context){ 0 }; would initialize ctx to point to a non-existent object (a dangling pointer). That's
// what the compiler is complaining about. The solution could be to give this initial context a name at global or
// function scope
Type init_ty = (Type){TY_INT, 8};
Type *ty_int = &init_ty;
Type init_bool_ty = (Type){TY_INT, 1};
Type *ty_char = &init_bool_ty;

bool is_integer(Type *ty) { return ty->kind == TY_INT || ty->kind == TY_CHAR; }

Type *copy_type(Type *ty) {
  Type *ret = (Type *)calloc(1, sizeof(Type));
  *ret = *ty;
  return ret;
}

Type *pointer_to(Type *base) {
  Type *ty = (Type *)calloc(1, sizeof(Type));
  ty->kind = TY_PTR;
  ty->base = base;
  ty->size = 8;
  return ty;
}

Type *func_type(Type *return_ty) {
  Type *ty = (Type *)calloc(1, sizeof(Type));
  ty->kind = TY_FUNC;
  ty->return_ty = return_ty;
  return ty;
}

Type *array_of(Type *base, int len) {
  Type *ty = (Type *)calloc(1, sizeof(Type));
  ty->kind = TY_ARRAY;
  ty->size = base->size * len;
  ty->base = base;
  ty->array_len = len;
  return ty;
}

void add_type(Node *node) {
  if (!node || node->ty) return;

  add_type(node->lhs);
  add_type(node->rhs);
  add_type(node->cond);
  add_type(node->then);
  add_type(node->els);
  add_type(node->init);
  add_type(node->inc);

  for (Node *n = node->body; n; n = n->next) add_type(n);
  for (Node *n = node->args; n; n = n->next) add_type(n);

  switch (node->kind) {
    case ND_ADD:
    case ND_SUB:
    case ND_MUL:
    case ND_DIV:
    case ND_NEG:
      node->ty = node->lhs->ty;
      return;
    case ND_ASSIGN:
      if (node->lhs->ty->kind == TY_ARRAY) error_tok(node->lhs->tok, "not an lvalue");
      node->ty = node->lhs->ty;
      return;
    case ND_EQ:
    case ND_NE:
    case ND_LT:
    case ND_LE:
    case ND_NUM:
    case ND_FUNCALL:
      node->ty = ty_int;
      return;
    case ND_VAR:
      node->ty = node->var->ty;
      return;
    case ND_ADDR:
      if (node->lhs->ty->kind == TY_ARRAY)
        node->ty = pointer_to(node->lhs->ty->base);
      else
        node->ty = pointer_to(node->lhs->ty);
      return;
    case ND_DEREF:
      if (!node->lhs->ty->base) error_tok(node->tok, "invalid pointer dereference");
      node->ty = node->lhs->ty->base;
      return;
  }
}