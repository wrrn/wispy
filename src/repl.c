#include "mpc/mpc.h"
#include <stdio.h>
#include <stdlib.h>

#include <editline/readline.h>
#ifdef __linux__
#include <editline/history.h>
#endif



int main(int argc, char **argv) {

  /* Create some parsers */
  mpc_parser_t *Number = mpc_new("number");
  mpc_parser_t *Operator = mpc_new("operator");
  mpc_parser_t *Expr = mpc_new("expr");
  mpc_parser_t *Lispy = mpc_new("lispy");

  mpca_lang(MPCA_LANG_DEFAULT,
            "                                                           \
                number : /-?[0-9]+/ ;                                   \
                operator : '+' | '-' | '*' | '/' | '%';                 \
                expr: <number> | '(' <operator>  <expr>+ ')' ;          \
                lispy: /^/ <operator> <expr>+ /$/ ;                     \
            ",
            Number, Operator, Expr, Lispy);

  
  /* Print Version and Exit information */  
  puts("Wispy Version 0.0.0.0.1");
  puts("It's amazing you should use it!");
  puts("Press Ctrl+c to Exit\n");

  /*In a never ending loop */
  while(1) {

    /*Output our prompt and get input */
    char *input = readline("wispy> ");

    /* Add input to history */
    add_history(input);

      
    /* Attempt to Parse the user Input */
    mpc_result_t r;
    if(mpc_parse("<stdin>", input, Lispy, &r)) {
      /* On Success print the AST */
      mpc_ast_print(r.output);
      mpc_ast_delete(r.output);
    } else {
      /* Otherwise print error */
      mpc_err_print(r.error);
      mpc_err_delete(r.error);
    }
    

    /* Free retrieved input */
    free(input);
  }

  return 0;

}


