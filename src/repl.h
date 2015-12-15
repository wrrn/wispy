#ifndef wispy_h
#define wispy_h

#include "mpc/mpc.h"
#include <stdio.h>
#include <stdlib.h>

#include <editline/readline.h>
#ifdef __linux__
#include <editline/history.h>
#endif

long eval(mpc_ast_t* t);
long eval_op(long x, char *op, long y);
#endif
