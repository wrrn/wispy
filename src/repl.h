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

#define LASSERT_TYPE( func, arg, expected)                  \
  LASSERT(arg, arg->type == expected,                       \
          "Function '%s' passed incorrect type. "           \
          "Expected %s, but got %s.",                       \
          func,                                             \
          ltype_name(arg->type), ltype_name(expected))

#define LASSERT_EXPR(func, args)                                                \
  LASSERT(args, args->type == LVAL_SEXPR || args->type == LVAL_QEXPR,           \
          "Function '%s' passed incorrect type. "                               \
          "Expected %s or %s, but got %s",                                      \
          func, ltype_name(LVAL_SEXPR), ltype_name(LVAL_QEXPR),ltype_name(args->type))


#define LASSERT_NUM(func, args, num)                            \
  LASSERT(args, get_expr(args)->count == num,                   \
          "Function '%s' passed incorrect number of arguments." \
          "Expected %d, but got %d",                            \
          func, num, get_expr(args)->count);

#define LASSERT_ARG_TYPE(func, args, argnum, expected)               \
  LASSERT(args, get_expr(args)->exprs[argnum]->type == expected,     \
          "Function '%s' passed illegal argument %d. "               \
          "Expected %s, but got %s",                                 \
          func, argnum, ltype_name(expected),                        \
          ltype_name(get_expr(args)->exprs[argnum]->type));


  



/* Enumeration of possible lval type */
typedef enum { LVAL_ERR, LVAL_NUM, LVAL_SYM, LVAL_STR, LVAL_FUN, LVAL_BUILTIN, LVAL_SEXPR, LVAL_QEXPR, LVAL_BOOL, LVAL_OK } lval_type;

struct lval;
struct lenv;
typedef struct lval lval;
typedef struct lenv lenv;
typedef char * lerr;
typedef char * lsym;
typedef char * lstr;



typedef lval*(*lbuiltin)(lenv*, lval*); 

/* A S-exp for wispy */
typedef struct lextended_expr {
  int count;
  struct lval** exprs;
} lextended_expr;

typedef lextended_expr lsexpr;
typedef lextended_expr lqexpr;

typedef struct lfunction {
  lval *formals;
  lenv *env;
  lval *body;
} lfunction;

typedef union lexpr {
  /* Define the atom */
  double num;
  lerr err;
  lsym sym;
  lstr str;
  /* End atom definition */
  lsexpr *sexpr;
  lqexpr *qexpr;
  lbuiltin builtin;
  lfunction *func;
  
} lexpr; 

/* A value for wispy */
typedef struct lval {
  lval_type type;
  lexpr expr;
} lval;


struct lenv {
  lenv* par;
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

/* Build user defined func */
lval* lval_lambda(lval* formals, lval* body);

/* Build boolean type */
lval* lval_bool(double x);

/* Build string type */
lval* lval_str(char *s);

/* Build OK type */
lval* lval_ok();

/** End Constructors **/

/** Destructor **/
/* Tear down lval */
void exprs_del(int count, lval** exprs);
void lval_del(lval* v);
/** End Destructor **/

/* Utility functions */
lextended_expr *get_expr(lval* v);

/* Copy an lval */
lval* lval_copy(lval* v);

lextended_expr* lextended_expr_copy(lextended_expr* e);

/* Add a new lval to a sexpr */
lextended_expr* lval_add(lsexpr* v, lval *x);

/* Read number into lval */
lval *lval_read_num(mpc_ast_t *t);

/* Read lval */
lval *lval_read(mpc_ast_t *t);

/* Get a lval string from mpc_ast_t */
lval *lval_read_str(mpc_ast_t *t);


/* Print an lval */
void lval_expr_print(lextended_expr *expr, char open, char close);
void lval_print(lval* v);
void lval_println(lval* v);
void lval_print_str(char*);

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
lval* builtin_add(lenv *e, lval *v);
lval* builtin_sub(lenv *e, lval *v);
lval* builtin_mul(lenv *e, lval *v);
lval* builtin_div(lenv *e, lval *v);

/* Builtin list functions */
lval* builtin_head(lenv *e, lval *v);
lval* qexpr_head(lval*);
lval* str_head(lval*);
lval* builtin_tail(lenv *e,lval *v);
lval* qexpr_tail(lval *v);
lval* str_tail(lval *v);
lval* builtin_list(lenv *e,lval *v);
lval* builtin_eval(lenv *e, lval *v);
lval* builtin_join(lenv *e, lval* v);
lval* lval_join(lval* x, lval* y);
lval* str_join(lval*, lval*);
lval* builtin_cons(lenv *e, lval *a);
lval* builtin_init(lenv *e, lval *a);
lval* builtin_len(lenv *e, lval *a);

/* Function utility functions */
lval* builtin_def(lenv *e, lval *a);
lval* builtin_lambda(lenv *e, lval *a);
lval* builtin_put(lenv *e, lval *a);
lval* lval_call(lenv *e, lval *f, lval *sexpr);
lval* builtin_print(lenv*, lval*);
lval* builtin_show(lenv*, lval*);
lval *builtin_err(lenv*, lval*);


/* Builtin Ordering function */
lval* builtin_not(lenv*, lval*);
lval* builtin_eq(lenv*, lval*);
lval* builtin_not_eq(lenv*, lval*);
lval* builtin_lt(lenv*, lval*);
lval* builtin_le(lenv*, lval*);
lval* builtin_gt(lenv*, lval*);
lval* builtin_ge(lenv*, lval*);
lval* builtin_ord(lenv *e, lval *v, char *op, double(*func)(double, double));
double num_lt(double, double);
double num_le(double, double);
double num_gt(double, double);
double num_ge(double, double);
double num_eq(double, double);
double lval_eq(lval*, lval*);
double expr_eq(lextended_expr*, lextended_expr*);

/* File loading function */
lval *builtin_load(lenv*, lval*);

/* String to Qexpr */
lval* builtin_read(lenv*, lval*);
  

/* Lenv functions */
lenv* lenv_new(void);
void lenv_del(lenv* e);
lval* lenv_get(lenv *e, lval *k);
void lenv_put(lenv *e, lval* k, lval *v);
void lenv_def(lenv *e, lval* k, lval *v);
lenv* lenv_copy(lenv *e);
void lenv_add_builtin(lenv *e, char* name, lbuiltin func);
void lenv_add_builtins(lenv *e);



/* Debugging/Error Utilities */
char *ltype_name(int t);


mpc_parser_t *Number;
mpc_parser_t *Symbol;
mpc_parser_t *String;
mpc_parser_t *Comment;
mpc_parser_t *Sexpr;
mpc_parser_t *Qexpr;
mpc_parser_t *Expr;
mpc_parser_t *Lispy;


static char const * const LANGDEF =
  "                                                                                      \
                number : /-?[0-9]+(\\.?[0-9]+)?/ ;                                       \
                symbol : /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&]+/ ;                              \
                string : /\"(\\\\.|[^\"])*\"/ ;                                          \
                comment: /;[^\\r\\n]*/ ;                                                 \
                sexpr  : '(' <expr>* ')' ;                                               \
                qexpr  : '{' <expr>* '}' ;                                               \
                expr   : <number> | <symbol> | <sexpr> | <qexpr> | <string> | <comment> ; \
                lispy  : /^/ <expr>* /$/ ;                                               \
  ";

#endif
