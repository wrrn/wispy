#ifndef wispy_h
#define wispy_h

#include "mpc/mpc.h"
#include <stdio.h>
#include <stdlib.h>

#include <editline/readline.h>
#ifdef __linux__
#include <editline/history.h>
#endif

/* Enumeration of possible lval type */
enum { LVAL_NUM, LVAL_ERR };


/* Enumberation of possible error types */
enum { LERR_DIV_ZERO, LERR_BAD_OP, LERR_BAD_NUM };

/* A value for wispy */
typedef struct {
  int type;
  long num;
  int err;
} lval;

/* Build lval number */
lval lval_num(long x);

/* Build lval err */
lval lval_err(int err);

/* Print an lval */
void lval_print(lval v);
void lval_println(lval v);

lval eval(mpc_ast_t* t);
lval eval_op(lval x, char *op, lval y);

static char const * const LANGDEF =
  "                                                                     \
                number : /-?[0-9]+/ ;                                   \
                operator : '+' | '-' | '*' | '/' | '%' ;                \
                expr: <number> | '(' <operator>  <expr>+ ')' ;          \
                lispy: /^/ <operator> <expr>+ /$/ ;                     \
  ";

#endif
