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
Type init_ty = (Type){TY_INT};
Type *ty_int = &init_ty;

bool is_integer(Type *ty) { return ty->kind == TY_INT; }

Type *pointer_to(Type *base) {
  Type *ty = (Type *)calloc(1, sizeof(Type));
  ty->kind = TY_PTR;
  ty->base = base;
  return ty;
}

Type *func_type(Type *return_ty) {
  Type *ty = (Type*)calloc(1, sizeof(Type));
  ty->kind = TY_FUNC;
  ty->return_ty = return_ty;
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

  switch (node->kind) {
    case ND_ADD:
    case ND_SUB:
    case ND_MUL:
    case ND_DIV:
    case ND_NEG:
    case ND_ASSIGN:
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
      node->ty = pointer_to(node->lhs->ty);
      return;
    case ND_DEREF:
      if (node->lhs->ty->kind != TY_PTR) error_tok(node->tok, "invalid pointer dereference");
      node->ty = node->lhs->ty->base;
      return;
  }
}