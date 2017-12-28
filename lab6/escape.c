#include <stdio.h>
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "escape.h"
#include "table.h"

typedef struct escapeEntry_ *escapeEntry;

struct escapeEntry_{
  int depth;
  bool* escape;
};

static escapeEntry EscapeEntry(int depth, bool* escape);

static escapeEntry EscapeEntry(int depth, bool* escape) {
  escapeEntry entry = checked_malloc(sizeof(*entry));
  entry->depth = depth;
  entry->escape = escape;
  return entry;
}

static void traverseExp(S_table env, int depth, A_exp e);
static void traverseDec(S_table env, int depth, A_dec d);
static void traverseVar(S_table env, int depth, A_var v);

void Esc_findEscape(A_exp exp) {
	//your code here
  traverseExp(S_empty(), 0, exp);
}

static void traverseExp(S_table env, int depth, A_exp e) {
  switch(e->kind){
    case A_varExp:
      traverseVar(env, depth, e->u.var);
      break;
    case A_nilExp:
    case A_intExp:
    case A_stringExp:
    case A_breakExp:
    case A_voidExp:
      break;
    case A_callExp: {
      A_expList args;
      for(args = e->u.call.args; args; args = args->tail) {
        traverseExp(env, depth, args->head);
      }
      break;
    }
    case A_opExp:
      traverseExp(env, depth, e->u.op.left);
      traverseExp(env, depth, e->u.op.right);
      break;
    case A_recordExp: {
      for(A_efieldList efields = e->u.record.fields; efields; efields = efields->tail) {
        traverseExp(env, depth, efields->head->exp);
      }
      break;
    }
    case A_seqExp: {
      for(A_expList exps = e->u.seq; exps; exps = exps->tail) {
        traverseExp(env, depth, exps->head);
      }
      break;
    }
    case A_assignExp:
      traverseVar(env, depth, e->u.assign.var);
      traverseExp(env, depth, e->u.assign.exp);
      break;
    case A_ifExp:
      traverseExp(env, depth, e->u.iff.test);
      traverseExp(env, depth, e->u.iff.then);
      if(e->u.iff.elsee){
        traverseExp(env, depth, e->u.iff.elsee);
      }
      break;
    case A_whileExp:
      traverseExp(env, depth, e->u.whilee.test);
      traverseExp(env, depth, e->u.whilee.body);
      break;
    case A_forExp:
      traverseExp(env, depth, e->u.forr.lo);
      traverseExp(env, depth, e->u.forr.hi);
      S_beginScope(env);
      e->u.forr.escape = FALSE;
      S_enter(env, e->u.forr.var, EscapeEntry(depth, &(e->u.forr.escape)));
      traverseExp(env, depth, e->u.forr.body);
      S_endScope(env);
      break;
    case A_letExp: {
      S_beginScope(env);
      A_decList decs;
      for(decs = e->u.let.decs; decs; decs = decs->tail) {
        traverseDec(env, depth, decs->head);
      }
      traverseExp(env, depth, e->u.let.body);
      S_endScope(env);
      break;
    }
    case A_arrayExp:
      traverseExp(env, depth, e->u.array.size);
      traverseExp(env, depth, e->u.array.init);
      break;
    default:
      assert(0);
  }
}

static void traverseDec(S_table env, int depth, A_dec d) {
  switch(d->kind) {
    case A_functionDec: {
      A_fundecList fundecs;
      for(fundecs = d->u.function; fundecs; fundecs = fundecs->tail) {
        S_beginScope(env);
        A_fieldList params;
        for(params = fundecs->head->params; params; params = params->tail) {
          params->head->escape = FALSE;
          S_enter(env, params->head->name, EscapeEntry(depth + 1, &(params->head->escape)));
        }
        traverseExp(env, depth + 1, fundecs->head->body);
        S_endScope(env);
      }
      break;
    }
    case A_varDec:
      traverseExp(env, depth, d->u.var.init);
      d->u.var.escape = FALSE;
      S_enter(env, d->u.var.var, EscapeEntry(depth, &(d->u.var.escape)));
      break;
    case A_typeDec:
      break;
    default:
      assert(0);
  }
}

static void traverseVar(S_table env, int depth, A_var v) {
  switch(v->kind) {
    case A_simpleVar: {
      escapeEntry entry = S_look(env, v->u.simple);
      if(depth > entry->depth) {
        *(entry->escape) = TRUE;
      }
      break;
    }
    case A_fieldVar: {
      traverseVar(env, depth, v->u.field.var);
      break;
    }
    case A_subscriptVar: {
      traverseVar(env, depth, v->u.subscript.var);
      traverseExp(env, depth, v->u.subscript.exp);
      break;
    }
    default:
      assert(0);
  }
}
