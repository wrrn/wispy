// -*- compile-command: "gcc -std=c11 -Wall -Wno-gnu -pedantic repl.c mpc/mpc.c -lm -ledit -o wispy"; -*-
#include "repl.h"

lval eval(mpc_ast_t* t) {
  /* If tagged a number returns directly */
  if (strstr(t->tag, "number")) {
    long num = strtol(t->contents, NULL, 10);
    return errno != ERANGE ? lval_num(num) : lval_err(LERR_BAD_NUM);

  }

  char *op = t->children[1]->contents;
  lval x = eval(t->children[2]);

  int i = 3;

  while (strstr(t->children[i]->tag, "expr")) {
    x = eval_op(x, op, (eval(t->children[i])));
    i += 1;
  }

  return x;

  
}

lval eval_op(lval x, char *op, lval y) {
  /* Verify that both lvals are not errors */
  if (x.type == LVAL_ERR) { return x; }
  if (y.type == LVAL_ERR) { return y; }

  /* Do the math on the number values */
  if (strcmp(op, "+") == 0) { return lval_num( x.num + y.num ); }
  if (strcmp(op, "-") == 0) { return lval_num( x.num - y.num ); }
  if (strcmp(op, "*") == 0) { return lval_num( x.num * y.num ); }
  if (strcmp(op, "/") == 0) {
    return y.num == 0
      ? lval_err(LERR_DIV_ZERO)
      : lval_num( x.num / y.num );

  }
  if (strcmp(op, "%") == 0) { return lval_num( x.num % y.num ); }
  return lval_err(LERR_BAD_OP);
}

lval lval_num(long x) {
  lval v;
  v.type = LVAL_NUM;
  v.num = x;
  return v;
}

lval lval_err(int err) {
  lval v;
  v.type = LVAL_ERR;
  v.err = err;
  return v;
}

void lval_print(lval v) {
  switch (v.type) {
  case LVAL_NUM:
    printf("%li", v.num);
    break;
  case LVAL_ERR:
    if (v.err == LERR_DIV_ZERO) {
      printf("Error: Division by Zero!");
    }
    if (v.err == LERR_BAD_OP) {
      printf("Error: Invalid Operator!");
    }
    if (v.err == LERR_BAD_NUM) {
      printf("Error: Invald Number!");
    }
    break;
      
  }
}

void lval_println(lval v) {
  lval_print(v);
  putchar('\n');
}

int main(int argc, char **argv) {

  /* Create some parsers */
  mpc_parser_t *Number = mpc_new("number");
  mpc_parser_t *Operator = mpc_new("operator");
  mpc_parser_t *Expr = mpc_new("expr");
  mpc_parser_t *Lispy = mpc_new("lispy");

  mpca_lang(MPCA_LANG_DEFAULT,
            LANGDEF,
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
      lval result = eval(r.output);
      lval_println(result);
      mpc_ast_delete(r.output);
    } else {
      /* Otherwise print error */
      mpc_err_print(r.error);
      mpc_err_delete(r.error);
    }
    

    /* Free retrieved input */
    free(input);
  }

  mpc_cleanup(4, Number, Operator, Expr, Lispy);

  return 0;

}
