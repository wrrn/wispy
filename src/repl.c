// -*- compile-command: "gcc -std=c11 -Wall -Wno-gnu -pedantic repl.c mpc/mpc.c -lm -ledit -o wispy"; -*-
#include "repl.h"

lval* lval_eval_sexpr(lval* v) {
   lsexpr* s = v->expr.sexpr; 
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

  lval* result = builtin_op(v, f->expr.sym);
  lval_del(f);
  return result;
} 

lval* lval_eval(lval* v) {
  if (v->type == LVAL_SEXPR) {
    return lval_eval_sexpr(v);
  } 
 return v; 
} 

lval *lval_pop(lsexpr *s, int index) { 
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

void lval_del(lval* v) {
  switch (v->type) {
  case LVAL_NUM: break;
  case LVAL_ERR:
    free(v->expr.err);
    break;
  case LVAL_SYM:
    free(v->expr.sym);
    break;
  case LVAL_SEXPR:
    for (int i = 0; i < v->expr.sexpr->count; i++) {
      lval_del(v->expr.sexpr->exprs[i]);
    }
    free(v->expr.sexpr->exprs);
    free(v->expr.sexpr);
    break;
  }

  free(v);
  v = NULL;
}

lsexpr* lval_add(lsexpr* s, lval *x) {

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

void lval_expr_print(lval* v, char open, char close) {
  printf("%c ", open);
  int count = v->type == LVAL_SEXPR ? v->expr.sexpr->count : 0;
  for (int i = 0; i < count; i++) {
    lval_print(v->expr.sexpr->exprs[i]);
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
  case LVAL_SEXPR:
    lval_expr_print(v, '(', ')');
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
  mpc_parser_t *Expr = mpc_new("expr");
  mpc_parser_t *Lispy = mpc_new("lispy");

  mpca_lang(MPCA_LANG_DEFAULT,
            LANGDEF,
            Number, Symbol, Sexpr, Expr, Lispy);

  
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

  mpc_cleanup(5, Number, Symbol, Sexpr, Expr, Lispy);

  return 0;

}
