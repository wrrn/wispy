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

#define LASSERT(args, cond, fmt, ...)           \
  if (!(cond)) {                                \
    lval *err =  lval_err(fmt, ##__VA_ARGS__);  \
    lval_del(args);                             \
    return err;                                 \
  }

/* Enumeration of possible lval type */
typedef enum { LVAL_ERR, LVAL_NUM, LVAL_SYM, LVAL_FUN, LVAL_SEXPR, LVAL_QEXPR } lval_type;

struct lval;
struct lenv;
typedef struct lval lval;
typedef struct lenv lenv;
typedef char * lerr;
typedef char * lsym;



typedef lval*(*lbuiltin)(lenv*, lval*); 

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
  lbuiltin fun;
  
} lexpr; 

/* A value for wispy */
typedef struct lval {
  lval_type type;
  lexpr expr;
} lval;


struct lenv {
  int count;
  char **syms;
  lval** vals;
};

/** Constructors **/
/* Build lval number */
lval* lval_num(double x);

/* Build lval err */
lval* lval_err(char* fmt, ...);

/* Build lval symbol */
lval* lval_sym(lsym sym);

/* Build lval Sexpr */
lval* lval_sexpr(void);

/* Build lval Qexpr */
lval* lval_qexpr(void);

/* Build lval builtin func */
lval* lval_fun(lbuiltin func);

/** End Constructors **/

/** Destructor **/
/* Tear down lval */
void exprs_del(int count, lval** exprs);
void lval_del(lval* v);
/** End Destructor **/

/* Copy an lval */
lval* lval_copy(lval* v);

lextended_expr* lextended_expr_copy(lextended_expr* e);

/* Add a new lval to a sexpr */
lextended_expr* lval_add(lsexpr* v, lval *x);

/* Read number into lval */
lval *lval_read_num(mpc_ast_t *t);

/* Read lval */
lval *lval_read(mpc_ast_t *t);

/* Print an lval */
void lval_expr_print(lextended_expr *expr, char open, char close);
void lval_print(lval* v);
void lval_println(lval* v);

/* Evaluation of Sexpr */
lval* lval_eval_sexpr(lenv* e, lval* v);

/* Evaluation of lval */
lval* lval_eval(lenv* e, lval *v);

/* Pop something out of Sexpr cells */
lval* lval_pop(lextended_expr *s, int index);

/* Take something from an lval and the delete the containing lval */
lval* lval_take(lval *v, int index);

/* Evaluation of builtin operations */
lval* builtin(lenv *e, lval* a, char* func);
lval* builtin_op(lenv *e, lval* v, lsym sym);

/* Builtin mathmatical functions */
lval *builtin_add(lenv *e, lval *v);
lval *builtin_sub(lenv *e, lval *v);
lval *builtin_mul(lenv *e, lval *v);
lval *builtin_div(lenv *e, lval *v);

/* Builtin list functions */
lval* builtin_head(lenv *e, lval *v);
lval* builtin_tail(lenv *e,lval *v);
lval* builtin_list(lenv *e,lval *v);
lval* builtin_eval(lenv *e, lval *v);
lval* builtin_join(lenv *e, lval* v);
lval* lval_join(lval* x, lval* y);
lval* builtin_cons(lenv *e, lval *a);
lval* builtin_init(lenv *e, lval *a);
lval* builtin_len(lenv *e, lval *a);

/* Function utility functions */
lval* builtin_def(lenv* e, lval *a);

/* Lenv functions */
lenv* lenv_new(void);
void lenv_del(lenv* e);
lval* lenv_get(lenv *e, lval *k);
void lenv_put(lenv *e, lval* k, lval *v);
void lenv_add_builtin(lenv *e, char* name, lbuiltin func);
void lenv_add_builtins(lenv *e);

/* Debugging/Error Utilities */
char *ltype_name(int t);



static char const * const LANGDEF =
  "                                                                     \
                number : /-?[0-9]+(\\.?[0-9]+)?/ ;                      \
                symbol : /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&]+/ ;             \
                sexpr  : '(' <expr>* ')' ;                              \
                qexpr  : '{' <expr>* '}' ;                              \
                expr   : <number> | <symbol> | <sexpr> | <qexpr> ;      \
                lispy  : /^/ <expr>* /$/ ;                              \
  ";

#endif
