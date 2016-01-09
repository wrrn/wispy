// -*- compile-command: "gcc -std=c11 -Wall -Wno-gnu -pedantic repl.c mpc/mpc.c -lm -ledit -o wispy"; -*-
#include "repl.h"

lval* lval_eval_sexpr(lval* v) {
  assert(v->type == LVAL_SEXPR);
  lsexpr* s = v->expr.sexpr;

  for (int i = 0; i < s->count; i++) {
    s->exprs[i] = lval_eval(s->exprs[i]);
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
  if (f->type != LVAL_SYM) {
    lval_del(f);
    lval_del(v);
    return lval_err("S-expression does not start with symbol!");
  }

  lval* result = builtin(v, f->expr.sym);
  lval_del(f);
  return result;
} 

lval* lval_eval(lval* v) {
  if (v->type == LVAL_SEXPR) {
    return lval_eval_sexpr(v);
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

lval* builtin(lval *v, char* func) {
  if (strcmp("list", func) == 0) { return builtin_list(v); }
  if (strcmp("head", func) == 0) { return builtin_head(v); }
  if (strcmp("tail", func) == 0) { return builtin_tail(v); }
  if (strcmp("join", func) == 0) { return builtin_join(v); }
  if (strcmp("eval", func) == 0) { return builtin_eval(v); }
  if (strcmp("cons", func) == 0) { return builtin_cons(v); }
  if (strcmp("len", func) == 0) { return builtin_len(v); }
  if (strcmp("init", func) == 0) { return builtin_init(v); }
  if (strstr("+-/*", func)) { return builtin_op(v, func); }
  lval_del(v);
  return lval_err("Unknown Function!");  
}

lval *builtin_op(lval *v, lsym sym) {
  lsexpr *sexpr;
  assert(v->type == LVAL_SEXPR);
  sexpr = v->expr.sexpr;
  for (int i = 0; i < sexpr->count; i++) {
    if (sexpr->exprs[i]->type != LVAL_NUM) {
      lval_del(v);
      return lval_err("Cannot operate on non-number!");
    }
  }

  lval *x = lval_pop(sexpr, 0);

  if (strcmp(sym, "-") == 0 && sexpr->count == 0) {
    x->expr.num = -(x->expr.num);
  }

  while (sexpr->count > 0) {
    lval *y = lval_pop(sexpr, 0);

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

lval* builtin_head(lval *a) {
  lextended_expr* expr;
  LASSERT(a, a->type == LVAL_SEXPR || a->type == LVAL_QEXPR, "Function 'head' passed illegal type");
  expr = a->type == LVAL_SEXPR ? a->expr.sexpr : a->expr.qexpr;
  LASSERT(a, expr->count == 1, "Function 'head' passed to many arguments");
  LASSERT(a, expr->exprs[0]->type == LVAL_QEXPR, "Function 'head' passed incorrect type");
  LASSERT(a, expr->exprs[0]->expr.qexpr->count != 0, "Function 'head' passed {}!");

  lval* v = lval_take(a, 0);
  lqexpr* qexpr = v->expr.qexpr;
  while (qexpr->count > 1 ) {
    lval_del(lval_pop(qexpr, 1));
  }
  return v;
}

lval* builtin_tail(lval *a) {
  lextended_expr* expr;
  LASSERT(a, a->type == LVAL_SEXPR || a->type == LVAL_QEXPR, "Function 'tail' passed illegal type");
  expr = a->type == LVAL_SEXPR ? a->expr.sexpr : a->expr.qexpr;
  LASSERT(a, expr->count == 1, "Function 'head' passed to many arguments");
  LASSERT(a, expr->exprs[0]->type == LVAL_QEXPR, "Function 'head' passed incorrect type");
  LASSERT(a, expr->exprs[0]->expr.qexpr->count != 0, "Function 'head' passed {}!");

  lval* v = lval_take(a, 0);
  lval_del(lval_pop(v->expr.qexpr,0));
  return v;
 
  
}

lval* builtin_list(lval *a) {
  LASSERT(a, a->type == LVAL_SEXPR || a->type == LVAL_QEXPR, "Function 'list' passed illegal type");
  a->type = LVAL_QEXPR;
  return a;
}

lval* builtin_eval(lval *a) {
  lextended_expr* expr;
  LASSERT(a, a->type == LVAL_SEXPR || a->type == LVAL_QEXPR, "Function 'eval' passed illegal type");
  expr = a->type == LVAL_SEXPR ? a->expr.sexpr : a->expr.qexpr;
  LASSERT(a, expr->exprs[0]->type == LVAL_QEXPR, "Function 'eval' passed incorrect type");
  lval *x = lval_take(a, 0);
  x->type = LVAL_SEXPR;
  return lval_eval(x);
  
}

lval *builtin_cons(lval *a) {
  lextended_expr* expr;
  LASSERT(a, a->type == LVAL_SEXPR || a->type == LVAL_QEXPR, "Function 'cons' passed illegal type");
  expr = a->type == LVAL_SEXPR ? a->expr.sexpr : a->expr.qexpr;
  LASSERT(a, expr->count == 2, "Function 'cons' passed too many arguments!");
  LASSERT(a, expr->exprs[1]->type == LVAL_QEXPR, "Function 'cons' was passed an illegal type");
  lval *val = lval_pop(expr, 0);
  lval *expr_qexpr = lval_take(a, 0);
  lqexpr* qexpr = expr_qexpr->expr.qexpr;
  qexpr->count++;
  qexpr->exprs = realloc(qexpr->exprs, sizeof(lval*) * qexpr->count);
  memmove(&qexpr->exprs[1], &qexpr->exprs[0], sizeof(lval*) * (qexpr->count - 1));
  qexpr->exprs[0] = val;
  return expr_qexpr;
  
    
}

lval* builtin_len(lval *a) {
  lval* val;
  lextended_expr* expr;
  LASSERT(a, a->type == LVAL_SEXPR || a->type == LVAL_QEXPR, "Function 'len' passed illegal type");
  expr = a->type == LVAL_SEXPR ? a->expr.sexpr : a->expr.qexpr;
  LASSERT(a, expr->count == 1, "Function 'len' passed too many arguments!");
  LASSERT(a, expr->exprs[0]->type == LVAL_QEXPR, "Function 'len' was passed an illegal type");
  lval *qexpr = lval_take(a, 0);
  val = lval_num(qexpr->expr.qexpr->count);
  lval_del(qexpr);
  return val;
}

lval* builtin_init(lval *a) {
  lextended_expr* expr;
  LASSERT(a, a->type == LVAL_SEXPR || a->type == LVAL_QEXPR, "Function 'init' passed illegal type");
  expr = a->type == LVAL_SEXPR ? a->expr.sexpr : a->expr.qexpr;
  LASSERT(a, expr->count == 1, "Function 'init' passed too many arguments!");
  LASSERT(a, expr->exprs[0]->type == LVAL_QEXPR, "Function 'init' was passed an illegal type");
  lval* qexpr = lval_take(a, 0);
  lval* first = lval_pop(qexpr->expr.qexpr, 0);
  lval_del(first);
  return qexpr;
  
  
}

lval* builtin_join(lval* a) {
  lextended_expr* expr;
  LASSERT(a, a->type == LVAL_SEXPR || a->type == LVAL_QEXPR, "Function 'join' passed illegal type");
  expr = a->type == LVAL_SEXPR ? a->expr.sexpr : a->expr.qexpr;
  for (int i = 0; i < expr->count; i++) {
    LASSERT(a, expr->exprs[i]->type == LVAL_QEXPR, "Fucntion 'join' passed incorrect type");
  }

  lval* x = lval_pop(expr, 0);
  while ( expr->count ) {
    x = lval_join(x, lval_pop(expr, 0));
  }

  lval_del(a);
  return x;
}

lval* lval_join(lval *x, lval *y) {
  assert(x->type == LVAL_QEXPR && y->type == LVAL_QEXPR);
  lqexpr *y_qexpr = y->expr.qexpr;
  while(y_qexpr) {
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

lval* lval_err(lerr err) {
  lval *v = malloc(sizeof(lval));
  v->type = LVAL_ERR;
  v->expr.err = malloc(strlen(err) + 1);
  strcpy(v->expr.err, err);

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
  v->type = LVAL_FUN;
  v->expr.fun = func;
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
  case LVAL_FUN:
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
  case LVAL_FUN:
    printf("<function>");
    break;
  case LVAL_SEXPR:
    lval_expr_print(v->expr.sexpr, '(', ')');
    break;
  case LVAL_QEXPR:
    lval_expr_print(v->expr.qexpr, '{', '}');
    break;
  }
}

void lval_println(lval* v) {
  lval_print(v);
  putchar('\n');
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
      lval *x = lval_eval(lval_read(r.output));
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

  mpc_cleanup(6, Number, Symbol, Sexpr, Qexpr, Expr, Lispy);

  return 0;

}
