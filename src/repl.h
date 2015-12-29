#ifndef wispy_h
#define wispy_h

#include "mpc/mpc.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include <editline/readline.h>
#ifdef __linux__
#include <editline/history.h>
#endif

/* Enumeration of possible lval type */
typedef enum { LVAL_ERR, LVAL_NUM, LVAL_SYM, LVAL_SEXPR, LVAL_QEXPR } lval_type;

typedef char * lerr;
typedef char * lsym;


/* A S-exp for wispy */
typedef struct lextended_expr {
  int count;
  struct lval** exprs;
} lextended_expr;

typedef lextended_expr lsexpr;
typedef lextended_expr lqexpr;

typedef union lexpr {
  /* Define the atom */
  double num;
  lerr err;
  lsym sym;
  /* End atom definition */
  lsexpr *sexpr;
  lqexpr *qexpr;
} lexpr; 

/* A value for wispy */
typedef struct lval {
  lval_type type;
  lexpr expr;
} lval;


/** Constructors **/
/* Build lval number */
lval* lval_num(double x);

/* Build lval err */
lval* lval_err(lerr err);

/* Build lval symbol */
lval* lval_sym(lsym sym);

/* Build lval Sexpr */
lval* lval_sexpr(void);

lval* lval_qexpr(void);
/** End Constructors **/

/** Destructor **/
/* Tear down lval */
void exprs_del(int count, lval** exprs);
void lval_del(lval* v);
/** End Destructor **/

/* Add a new lval to a sexpr */
lsexpr* lval_add(lsexpr* v, lval *x);

/* Read number into lval */
lval *lval_read_num(mpc_ast_t *t);

/* Read lval */
lval *lval_read(mpc_ast_t *t);

/* Print an lval */
void lval_expr_print(lextended_expr *expr, char open, char close);
void lval_print(lval* v);
void lval_println(lval* v);

/* Evaluation of Sexpr */
lval* lval_eval_sexpr(lval* v);

/* Evaluation of lval */
lval* lval_eval(lval *v);

/* Pop something out of Sexpr cells */
lval* lval_pop(lsexpr *s, int index);

/* Take something from an lval and the delete the containing lval */
lval* lval_take(lval *v, int index);

/* Evaluation of builtin operations */
lval* builtin_op(lval* v, lsym sym);

static char const * const LANGDEF =
  "                                                                     \
                number : /-?[0-9]+(\\.?[0-9]+)?/ ;                      \
                symbol : '+' | '-' | '*' | '/' | '%' ;                  \
                sexpr  : '(' <expr>* ')' ;                              \
                expr   : <number> | <symbol> | <sexpr> ;                \
                qexpr  : '{' <expr>* '}' ;                              \
                expr   : <number> | <symbol> | <sexpr> | <qexpr> ;      \
                lispy  : /^/ <expr>* /$/ ;                              \
  ";

#endif
