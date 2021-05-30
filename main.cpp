#include "syscc.hpp"

int main(int argc, char **argv) {
  if (argc != 2) error("%s: invalid number of arguments", argv[0]);

  Token *tok = tokenize(argv[1]);
  Function *prog = parse(tok);
  // Print the AST
  dotgen(prog);
  // Traverse the AST to emit assembly.
  codegen(prog);
  return 0;
}