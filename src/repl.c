// -*- compile-command: "gcc -std=c11 -Wall -Wno-gnu -g -pedantic repl.c mpc/mpc.c -lm -ledit -o wispy"; -*-
#include "repl.h"

lval* lval_eval_sexpr(lenv* e, lval* v) {
  LASSERT_TYPE("lval_eval_sexpr", v, LVAL_SEXPR)
  lsexpr* s = v->expr.sexpr;

  for (int i = 0; i < s->count; i++) {
    s->exprs[i] = lval_eval(e, s->exprs[i]);
  }
  
  for (int i = 0; i < s->count; i++) { 
    if (s->exprs[i]->type == LVAL_ERR) { 
      return lval_take(v, i); 
    } 
  } 

  if (s->count == 0) {
    return v;
  }

  if (s->count == 1) {
    return lval_take(v, 0);
  }

  lval *f = lval_pop(s, 0);
  if (f->type != LVAL_FUN && f->type != LVAL_BUILTIN) {
    lval_del(f);
    lval_del(v);
    return lval_err("S-expression does not start with a function!");
  }
  
  lval* result = lval_call(e,f,v);
  lval_del(f);
  return result;
} 

lval* lval_eval(lenv *e, lval* v) {
  if (v->type == LVAL_SYM) {
    lval *x = lenv_get(e, v);
    lval_del(v);
    return x;
  }
  if (v->type == LVAL_SEXPR) {
    return lval_eval_sexpr(e, v);
  } 
  return v; 
} 

lval *lval_pop(lextended_expr *s, int index) { 
  lval *x = s->exprs[index];
  memmove(&s->exprs[index], &s->exprs[index+1], sizeof(lval*) * (s->count - index - 1));
  s->count--;
  s->exprs = realloc(s->exprs, sizeof(lval*) * s->count);
  return x;
} 

lval *lval_take(lval *v, int index) { 
  lval *x = lval_pop(v->expr.sexpr, index); 
  lval_del(v); 
  return x;     
} 

lval* builtin(lenv *e, lval *v, char* func) {
  if (strcmp("list", func) == 0) { return builtin_list(e, v); }
  if (strcmp("head", func) == 0) { return builtin_head(e, v); }
  if (strcmp("tail", func) == 0) { return builtin_tail(e, v); }
  if (strcmp("join", func) == 0) { return builtin_join(e, v); }
  if (strcmp("eval", func) == 0) { return builtin_eval(e, v); }
  if (strcmp("cons", func) == 0) { return builtin_cons(e, v); }
  if (strcmp("len", func) == 0) { return builtin_len(e, v); }
  if (strcmp("init", func) == 0) { return builtin_init(e, v); }
  if (strcmp("+", func) == 0 ) { return builtin_add(e, v); }
  if (strcmp("-", func) == 0 ) { return builtin_sub(e, v); }
  if (strcmp("*", func) == 0 ) { return builtin_mul(e, v); }
  if (strcmp("/", func) == 0 ) { return builtin_div(e, v); }
  lval_del(v);
  return lval_err("Unknown Function!");  
}

lval *builtin_op(lenv *e, lval *v, lsym sym) {
  lsexpr *sexpr;
  LASSERT_TYPE(sym, v, LVAL_SEXPR);
  sexpr = v->expr.sexpr;
  for (int i = 0; i < sexpr->count; i++) {
    LASSERT_ARG_TYPE("builtin op", v, i, LVAL_NUM);
  }

  lval *x = lval_eval(e, lval_pop(sexpr, 0));

  if (strcmp(sym, "-") == 0 && sexpr->count == 0) {
    x->expr.num = -(x->expr.num);
  }

  while (sexpr->count > 0) {
    lval *y = lval_eval(e, lval_pop(sexpr, 0));
    if (strcmp(sym, "+") == 0) { x->expr.num += y->expr.num; }
    if (strcmp(sym, "-") == 0) { x->expr.num -= y->expr.num; }
    if (strcmp(sym, "*") == 0) { x->expr.num *= y->expr.num; }
    if (strcmp(sym, "/") == 0) {
      if (y->expr.num == 0) {
        lval_del(x);
        lval_del(y);
        x = lval_err("Division by zero!");
        break;
      }
      x->expr.num /= y->expr.num;
    }
    lval_del(y);
  }

  lval_del(v);
  return x;

}

lval* builtin_add(lenv* e, lval* a) {
  return builtin_op(e, a, "+");
}

lval* builtin_sub(lenv* e, lval* a) {
  return builtin_op(e, a, "-");
}

lval* builtin_mul(lenv *e, lval *a) {
  return builtin_op(e, a, "*");
}

lval* builtin_div(lenv* e, lval* a) {
  return builtin_op(e, a, "/");
}


lval* builtin_head(lenv *e, lval *a) {
  LASSERT_EXPR("builtin_head", a);
  LASSERT_NUM("head", a, 1);
  LASSERT_ARG_TYPE("head", a, 0, LVAL_QEXPR);
  LASSERT(a, get_expr(a)->exprs[0]->expr.qexpr->count != 0, "Function 'head' passed {}!");

  lval* v = lval_take(a, 0);
  lqexpr* qexpr = v->expr.qexpr;
  while (qexpr->count > 1 ) {
    lval_del(lval_pop(qexpr, 1));
  }
  return v;
}


lval* builtin_tail(lenv *e, lval *a) {
  LASSERT_EXPR("tail", a);
  LASSERT_NUM("tail", a, 1);
  LASSERT_ARG_TYPE("tail",a, 0, LVAL_QEXPR);
  LASSERT(a, get_expr(a)->exprs[0]->expr.qexpr->count != 0, "Function 'tail' passed {}!");

  lval* v = lval_take(a, 0);
  lval_del(lval_pop(v->expr.qexpr,0));
  return v;
 
  
}

lval* builtin_list(lenv *e, lval *a) {
  LASSERT_EXPR("list", a);
  a->type = LVAL_QEXPR;
  return a;
}

lval* builtin_eval(lenv *e, lval *a) {
  LASSERT_EXPR("eval", a);
  LASSERT_ARG_TYPE("eval", a, 0, LVAL_QEXPR);
  lval *x = lval_take(a, 0);
  x->type = LVAL_SEXPR;
  return lval_eval(e, x);
  
}

lval *builtin_cons(lenv *e, lval *a) {
  LASSERT_EXPR("cons", a);
  LASSERT_NUM("cons", a, 2);
  LASSERT_ARG_TYPE("cons", a, 1, LVAL_QEXPR);
  lval *val = lval_pop(get_expr(a), 0);
  lval *expr_qexpr = lval_take(a, 0);
  lqexpr* qexpr = expr_qexpr->expr.qexpr;
  qexpr->count++;
  qexpr->exprs = realloc(qexpr->exprs, sizeof(lval*) * qexpr->count);
  memmove(&qexpr->exprs[1], &qexpr->exprs[0], sizeof(lval*) * (qexpr->count - 1));
  qexpr->exprs[0] = val;
  return expr_qexpr;
  
    
}

lval* builtin_len(lenv *e, lval *a) {
  lval* val;
  LASSERT_EXPR("len", a);
  LASSERT_NUM("len", a, 1);
  LASSERT_ARG_TYPE("len", a, 0, LVAL_QEXPR);
  lval *qexpr = lval_take(a, 0);
  val = lval_num(qexpr->expr.qexpr->count);
  lval_del(qexpr);
  return val;
}

lval* builtin_init(lenv *e, lval *a) {
  LASSERT_EXPR("init", a);
  LASSERT_NUM("init", a, 1);
  LASSERT_ARG_TYPE("init", a, 0, LVAL_QEXPR);
  lval* qexpr = lval_take(a, 0);
  lval* first = lval_pop(qexpr->expr.qexpr, 0);
  lval_del(first);
  return qexpr;
  
  
}

lval* builtin_join(lenv *e, lval* a) {
  lextended_expr* expr;
  LASSERT_EXPR("join", a);
  expr = get_expr(a);
  for (int i = 0; i < expr->count; i++) {
    LASSERT_ARG_TYPE("join", a, i, LVAL_QEXPR);
  }

  lval* x = lval_pop(expr, 0);
  while ( expr->count ) {
    x = lval_join(x, lval_pop(expr, 0));
  }

  lval_del(a);
  return x;
}

lval* builtin_lambda(lenv *e, lval *a){
  LASSERT_EXPR("\\", a);
  LASSERT_NUM("\\", a, 2);
  LASSERT_ARG_TYPE("\\", a, 0, LVAL_QEXPR);
  LASSERT_ARG_TYPE("\\", a, 1, LVAL_QEXPR);
  lextended_expr *expr = get_expr(a);
  lextended_expr *symbols_list = get_expr(expr->exprs[0]);
    for (int i = 0; i < symbols_list->count; i++) {
      int val_type = symbols_list->exprs[i]->type;
      LASSERT(a, val_type == LVAL_SYM,
              "Cannot define non-symbol. Got %s, expected %s",
              ltype_name(val_type), ltype_name(LVAL_SYM));
    }

  lval* formals = lval_pop(expr, 0);
  lval* body = lval_pop(expr, 0);
  lval_del(a);

  return lval_lambda(formals, body);
}

lval* lval_join(lval *x, lval *y) {
  LASSERT_TYPE("lval_join", x, LVAL_QEXPR);
  LASSERT_TYPE("lval_join", y, LVAL_QEXPR);

  lqexpr *y_qexpr = y->expr.qexpr;
  while(y_qexpr->count > 0) {
    x->expr.qexpr = lval_add(x->expr.qexpr, lval_pop(y_qexpr,0));
  }

  lval_del(y);
  return x;
}



lval* lval_num(double x) {
  lval *v = malloc(sizeof(lval));
  v->type = LVAL_NUM;
  v->expr.num = x;
  return v;
}

lval* lval_err(char *fmt, ...) {
  lval *v = malloc(sizeof(lval));
  v->type = LVAL_ERR;
  va_list va;
  va_start(va, fmt);
  v->expr.err = malloc(512);
  vsnprintf(v->expr.err, 511, fmt, va);
  v->expr.err = realloc(v->expr.err, strlen(v->expr.err)+1);
  va_end(va);
  return v;
}

lval* lval_sym(lsym s) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_SYM;
  v->expr.sym = malloc(strlen(s) + 1);
  strcpy(v->expr.sym, s);
  return v;
}


lval* lval_sexpr(void) {
  lval* v = malloc(sizeof(lval));
  v->expr.sexpr = malloc(sizeof(lsexpr));
  v->type = LVAL_SEXPR;
  v->expr.sexpr->count = 0;
  v->expr.sexpr->exprs = NULL;
  return v;
}

lval* lval_qexpr(void) {
  lval* v = malloc(sizeof(lval));
  v->expr.qexpr = malloc(sizeof(lqexpr));
  v->type = LVAL_QEXPR;
  v->expr.qexpr->count = 0;
  v->expr.qexpr->exprs = NULL;
  return v;

}

lval* lval_fun(lbuiltin func) {
  lval *v = malloc(sizeof(lval));
  v->type = LVAL_BUILTIN;
  v->expr.builtin = func;
  return v;
}


lval* lval_lambda(lval *formals, lval* body) {
  lval *v = malloc(sizeof(lval));
  lfunction *f = malloc(sizeof(lfunction));
  v->type = LVAL_FUN;
  f->env = lenv_new();
  f->formals = formals;
  f->body = body;
  v->expr.func = f;
  return v;
}

void lval_expr_del(lextended_expr* expr) {
  for (int i = 0; i < expr->count; i++) {
    free(expr->exprs[i]);
  }
  free(expr->exprs);
  free(expr);
}

void lval_del(lval* v) {
  switch (v->type) {
  case LVAL_NUM: break;
  case LVAL_ERR:
    free(v->expr.err);
    break;
  case LVAL_SYM:
    free(v->expr.sym);
    break;
  case LVAL_BUILTIN:
    break;
  case LVAL_FUN:
    lenv_del(v->expr.func->env);
    lval_del(v->expr.func->formals);
    lval_del(v->expr.func->body);
    free(v->expr.func);
    v->expr.func = NULL;
    break;
  case LVAL_SEXPR:
    lval_expr_del(v->expr.sexpr);
    break;
  case LVAL_QEXPR:
    lval_expr_del(v->expr.qexpr);
    break;
  }

  free(v);
  v = NULL;
}

lextended_expr *get_expr(lval* v) {
  return v->type == LVAL_SEXPR ? v->expr.sexpr : v->expr.qexpr;
}

lval* lval_copy(lval *v) {
  lval *x = malloc(sizeof(lval));
  lfunction *func;
  x->type = v->type;
  
  switch (v->type) {
  case LVAL_BUILTIN:
    x->expr.builtin = v->expr.builtin;
    break;
  case LVAL_FUN:
    func = malloc(sizeof(lfunction));
    func->env = lenv_copy(v->expr.func->env);
    func->formals = lval_copy(v->expr.func->formals);
    func->body = lval_copy(v->expr.func->body);
    x->expr.func = func;
    break;
  case LVAL_NUM:
    x->expr.num = v->expr.num;
    break;
  case LVAL_ERR:
    x->expr.err = malloc(strlen(v->expr.err) + 1);
    strcpy(x->expr.err, v->expr.err);
    break;
  case LVAL_SYM:
    x->expr.sym = malloc(strlen(v->expr.sym) +1);
    strcpy(x->expr.sym, v->expr.sym);
    break;
  case LVAL_SEXPR:
    x->expr.sexpr = lextended_expr_copy(v->expr.sexpr);
    break;
  case LVAL_QEXPR:
    x->expr.qexpr = lextended_expr_copy(v->expr.qexpr);
    break;
  }

  return x;
  
}

lextended_expr* lextended_expr_copy(lextended_expr* e) {
  lextended_expr *expr = malloc(sizeof(lextended_expr));
  expr->count = e->count;
  expr->exprs = malloc(sizeof(lval*) * expr->count);
  for (int i = 0; i < expr->count; i++) {
    expr->exprs[i] = lval_copy(e->exprs[i]);
  }

  return expr;
}

lextended_expr* lval_add(lextended_expr* s, lval *x) {
  s->count++;
  s->exprs = realloc(s->exprs, sizeof(lval*) * s->count);
  s->exprs[s->count - 1] = x;
  return s;
  
}

lval* lval_read_num(mpc_ast_t *t) {
  errno = 0;
  double x = strtod(t->contents, 0);
  return errno != ERANGE ?
    lval_num(x) : lval_err("invalid number");
}

lval* lval_read(mpc_ast_t *t) {
  if (strstr(t->tag, "number")) {
    return lval_read_num(t);
  }
  if (strstr(t->tag, "symbol")) {
    return lval_sym(t->contents);
  }
  
  lval* x = NULL;
  if (strcmp(t->tag, ">") == 0 || strstr(t->tag, "sexpr")) {
    x = lval_sexpr();
  }

  if (strstr(t->tag, "qexpr")) {
    x = lval_qexpr();
  }

  for (int i = 0; i < t->children_num; i++) {
    mpc_ast_t *child = t->children[i];
    if (strcmp(child->contents, "(") == 0) { continue; }
    if (strcmp(child->contents, ")") == 0) { continue; }
    if (strcmp(child->contents, "{") == 0) { continue; }
    if (strcmp(child->contents, "}") == 0) { continue; }
    if (strcmp(child->tag, "regex") == 0) { continue; }
    
    x->expr.sexpr = lval_add(x->expr.sexpr, lval_read(child));
  }
  return x;  
}



void lval_expr_print(lextended_expr *expr, char open, char close) {
  printf("%c ", open);
  int count = expr->count;
  for (int i = 0; i < count; i++) {
    lval_print(expr->exprs[i]);
    putchar (' ');
  }
  putchar(close);
}

void lval_print(lval *v) {
  switch (v->type) {
  case LVAL_NUM:
    printf("%.4f", v->expr.num);
    break;
  case LVAL_ERR:
    printf("Error: %s", v->expr.err);
    break;
  case LVAL_SYM:
    printf("%s", v->expr.sym);
    break;
  case LVAL_BUILTIN:
    printf("<builtin>");
    break;
  case LVAL_FUN:
    printf("(\\ "); lval_print(v->expr.func->formals);
    putchar(' '); lval_print(v->expr.func->body); putchar(')');
                      
    break;
  case LVAL_SEXPR:
    lval_expr_print(v->expr.sexpr, '(', ')');
    break;
  case LVAL_QEXPR:
    lval_expr_print(v->expr.qexpr, '{', '}');
    break;
  }
}

lval *lval_call(lenv *e, lval *f, lval *sexpr) {
  LASSERT_EXPR("call", sexpr);
  if (f->type == LVAL_BUILTIN) {
    return f->expr.builtin(e, sexpr);
  }

  lfunction *func = f->expr.func;
  lextended_expr *formals = get_expr(func->formals);
  lsexpr *a = get_expr(sexpr);
  

  int given = a->count;
  int total = formals->count;

  while (a->count) {
    if (formals->count == 0) {
      lval_del(sexpr);
      return lval_err(
                      "Function passed too many arguments"
                      "Got %i, Expected %i", given, total
                      );
    }

    lval *sym = lval_pop(formals, 0);

    /* Niladic parameter */
    if(strcmp(sym->expr.sym, "&") == 0) {
      LASSERT(sexpr, formals->count == 1,
                  "Function format invalid"
                  "Symbol '&' not followd by single symbol.");
      lval *nsym = lval_pop(formals, 0);
      lenv_put(func->env, nsym, builtin_list(e, sexpr));
      lval_del(sym);
      lval_del(nsym);
      break;
    }
    
    lval *val = lval_pop(a, 0);
    lenv_put(func->env, sym, val);

    lval_del(sym);
    lval_del(val);    
  }

  lval_del(sexpr);
  a = NULL;

  if ( formals->count > 0 && strcmp(formals->exprs[0]->expr.sym, "&") == 0) {
    if (formals->count != 2) {
      return lval_err("Function format invalid"
                      "Symbol '&' not followed by single symbol.");
    }
    // Pop of the '&' symbol
    lval_del(lval_pop(formals, 0));
    lval *sym = lval_pop(formals, 0);
    // Buid an empty list
    lval* val = lval_qexpr();
    lenv_put(func->env, sym, val);
    lval_del(sym);
    lval_del(val);
  }
  
  if (formals->count == 0) {
    func->env->par = e;
    lval *s = lval_sexpr();
    s->expr.sexpr = lval_add(get_expr(s), lval_copy(func->body));
    return builtin_eval(func->env, s);
  }

  return lval_copy(f);
  
    
}


void lval_println(lval* v) {
  lval_print(v);
  putchar('\n');
}

/* LEnv functions */
lenv* lenv_new(void) {
  lenv* e = malloc(sizeof(lenv));
  e->par = NULL;
  e->count = 0;
  e->syms = NULL;
  e->vals = NULL;
  return e;
    
}

void lenv_del(lenv *e) {
  for (int i = 0; i < e->count; i++) {
    free(e->syms[i]);
    lval_del(e->vals[i]);
  }
  free(e->syms);
  free(e->vals);
  free(e);
}

lval* lenv_get(lenv* e, lval *k) {
  if (k->type != LVAL_SYM){
    return lval_err("Illegal lval passed to lenv_get should be of type symbol");
  }
  for (int i = 0; i < e->count; i++ ){
    if (strcmp(e->syms[i], k->expr.sym) == 0){
      return lval_copy(e->vals[i]);
    }
  }

  if (e->par != NULL) {
    return lenv_get(e->par, k);
  }

  return lval_err("Unbound symbol '%s'", k->expr.sym);
}

void lenv_put(lenv* e, lval* k, lval* v) {
  for (int i = 0; i < e->count; i++) {
    if(strcmp(e->syms[i], k->expr.sym) == 0) {
      lval_del(e->vals[i]);
      e->vals[i] = lval_copy(v);
      return;
    }
  }

  e->count++;
  e->vals = realloc(e->vals, sizeof(lval*) * e->count);
  e->syms = realloc(e->syms, sizeof(char*) * e->count);
  e->vals[e->count - 1] = lval_copy(v);
  e->syms[e->count - 1] = malloc(strlen(k->expr.sym) + 1);
  strcpy(e->syms[e->count - 1], k->expr.sym);
    
}

void lenv_def(lenv *e, lval *k, lval* v) {
  if (e->par == NULL) {
    lenv_put(e,k,v);
    return;
  }
  lenv_put(e->par, k, v);
}

lenv* lenv_copy(lenv *e) {
  lenv *cpy = malloc(sizeof(lenv));
  cpy->par = e->par;
  cpy->count = e->count;
  cpy->syms = malloc(e->count * sizeof(char *));
  cpy->vals = malloc(e->count * sizeof(lval *));
  for (int i = 0; i < cpy->count; i++) {
    cpy->syms[i] = malloc(strlen(e->syms[i]) + 1);
    strcpy(cpy->syms[i], e->syms[i]);
    cpy->vals[i] = lval_copy(e->vals[i]);
  }

  return cpy;
}

lval *builtin_var(lenv *e, lval *a, char *func, void (*define_env)(lenv*, lval*, lval*)) {
  lqexpr *syms;
  lsexpr *sexpr;
      
  LASSERT_TYPE("def", a, LVAL_SEXPR);
  LASSERT_ARG_TYPE("def", a, 0, LVAL_QEXPR);  
  sexpr = a->expr.sexpr;
  syms = sexpr->exprs[0]->expr.qexpr;

  for( int i = 0; i < syms->count; i++) {
    LASSERT(a, syms->exprs[i]->type == LVAL_SYM, "Function '%s' cannot define non-symbol", func);
  }

  LASSERT(a, syms->count == sexpr->count - 1, "Function '%s' cannot define incorrect number of values to symbols", func);

  if (define_env != NULL) {
    for (int i = 0; i < syms->count; i++) {
      define_env(e, syms->exprs[i], sexpr->exprs[i+1]);
    }
  }

  lval_del(a);
  return lval_sexpr();
}

lval *builtin_def(lenv *e, lval *a) {
  return builtin_var(e, a, "def", lenv_def);
}

lval *builtin_put(lenv *e, lval *a) {
  return builtin_var(e, a, "=", lenv_put);
}

void lenv_add_builtin(lenv *e, char* name, lbuiltin func) {
  lval *k = lval_sym(name);
  lval *v = lval_fun(func);
  lenv_put(e, k, v);
  lval_del(k);
  lval_del(v);
}

void lenv_add_builtins(lenv *e) {
  /* List functions */
  lenv_add_builtin(e, "list", builtin_list);
  lenv_add_builtin(e, "head", builtin_head);
  lenv_add_builtin(e, "tail", builtin_tail);
  lenv_add_builtin(e, "eval", builtin_eval);
  lenv_add_builtin(e, "join", builtin_join);
  lenv_add_builtin(e, "init", builtin_init);
  lenv_add_builtin(e, "len", builtin_len);

  /* Mathmatical functions */
  lenv_add_builtin(e, "+", builtin_add);
  lenv_add_builtin(e, "-", builtin_sub);
  lenv_add_builtin(e, "*", builtin_mul);
  lenv_add_builtin(e, "/", builtin_div);

  /* Variable functions */
  lenv_add_builtin(e, "\\", builtin_lambda);
  lenv_add_builtin(e, "def", builtin_def);
  lenv_add_builtin(e, "=", builtin_put);
  
}


char *ltype_name(int t) {
  switch(t) {
  case LVAL_BUILTIN:
  case LVAL_FUN: return "Function";
  case LVAL_NUM: return "Number";
  case LVAL_SYM: return "Symbol";
  case LVAL_SEXPR: return "S-Expression";
  case LVAL_QEXPR: return "Q-Expression";
  default: return "Unknown";
  }
}

int main(int argc, char **argv) {

  /* Create some parsers */
  mpc_parser_t *Number = mpc_new("number");
  mpc_parser_t *Symbol = mpc_new("symbol");
  mpc_parser_t *Sexpr = mpc_new("sexpr");
  mpc_parser_t *Qexpr = mpc_new("qexpr");
  mpc_parser_t *Expr = mpc_new("expr");
  mpc_parser_t *Lispy = mpc_new("lispy");

  mpca_lang(MPCA_LANG_DEFAULT,
            LANGDEF,
            Number, Symbol, Sexpr, Qexpr, Expr, Lispy);

  
  /* Print Version and Exit information */  
  puts("Wispy Version 0.0.0.0.1");
  puts("It's amazing you should use it!");
  puts("Press Ctrl+c to Exit\n");

  lenv* e = lenv_new();
  lenv_add_builtins(e);
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
      lval *input = lval_read(r.output);
      lval_println(input);
      lval *x = lval_eval(e, input);
      lval_println(x);
      lval_del(x);
      mpc_ast_delete(r.output);
    } else {
      /* Otherwise print error */
      mpc_err_print(r.error);
      mpc_err_delete(r.error);
    }
    

    /* Free retrieved input */
    free(input);
  }
  lenv_del(e);
  mpc_cleanup(6, Number, Symbol, Sexpr, Qexpr, Expr, Lispy);

  return 0;

}
