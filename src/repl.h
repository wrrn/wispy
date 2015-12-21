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
typedef enum { LVAL_NUM, LVAL_ERR } lval_type;


/* Enumberation of possible error types */
typedef enum { LERR_DIV_ZERO, LERR_BAD_OP, LERR_BAD_NUM } err_type;

/* A value for wispy */
typedef struct {
  lval_type type;
  union {
    double num;
    err_type err;
  } val;
} lval;

/* Build lval number */
lval lval_num(double x);

/* Build lval err */
lval lval_err(err_type err);

/* Print an lval */
void lval_print(lval v);
void lval_println(lval v);

lval eval(mpc_ast_t* t);
lval eval_op(lval x, char *op, lval y);

static char const * const LANGDEF =
  "                                                                     \
                number : /-?[0-9]+(\\.?[0-9]+)?/ ;                      \
                symbol : '+' | '-' | '*' | '/' | '%' ;                  \
                sexpr  : '(' <expr>* ')' ;                              \
                expr   : <number> | <symbol> | <sexpr> ;                \
                lispy  : /^/ <expr>* /$/ ;                              \
  ";

#endif
