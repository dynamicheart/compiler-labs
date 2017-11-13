#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "helper.h"
#include "env.h"
#include "semant.h"

/*Lab4: Your implementation of lab4*/


typedef void* Tr_exp;
struct expty 
{
	Tr_exp exp; 
	Ty_ty ty;
};

//In Lab4, the first argument exp should always be **NULL**.
struct expty expTy(Tr_exp exp, Ty_ty ty)
{
	struct expty e;

	e.exp = exp;
	e.ty = ty;

	return e;
}

Ty_ty actual_ty(Ty_ty ty)
{
  while(ty && ty->kind == Ty_name){
    ty = ty->u.name.ty;
  }
  return ty;
}

Ty_tyList makeFormalTyList(S_table tenv, A_fieldList params)
{
  return NULL;
}

struct expty transVar(S_table venv, S_table tenv, A_var v)
{
  switch(v->kind){
    case A_simpleVar: 
      {
        E_enventry x = S_look(venv, v->u.simple);
        if(x && x->kind == E_varEntry){
          return expTy(NULL, actual_ty(x->u.var.ty));
        }else{
          EM_error(v->pos, "undefined variable %s", S_name(v->u.simple));
        }
      }
    case A_fieldVar:
      {

      }
    case A_subscriptVar:
      {

      }
  }
  assert(0);
}

struct expty transExp(S_table venv, S_table tenv, A_exp a)
{
  switch(a->kind){
    case A_opExp:
      {
        A_oper oper = a->u.op.oper;
        struct expty left = transExp(venv, tenv, a->u.op.left);
        struct expty right = transExp(venv, tenv, a->u.op.right);
        if(oper == A_plusOp){
          if(left.ty->kind != Ty_int){
            EM_error(a->u.op.left->pos, "integer required");
          }
          if(right.ty->kind != Ty_int){
            EM_error(a->u.op.right->pos, "integer required");
          }
          return expTy(NULL, Ty_Int());
        }
      }
    case A_letExp:
      {
        struct expty exp;
        A_decList d;
        S_beginScope(venv);
        S_beginScope(tenv);
        for(d = a->u.let.decs; d; d=d->tail){
          transDec(venv, tenv, d->head);
        }
        exp = transExp(venv, tenv, a->u.let.body);
        S_endScope(tenv);
        S_endScope(venv);
        return exp;
      }
    case A_varExp:
      {
      }
    case A_nilExp:
      {
      }
    case A_intExp:
      {
      }
    case A_stringExp:
      {
      }
    case A_callExp:
      {
      }
    case A_recordExp:
      {
      }
    case A_seqExp:
      {
      }
    case A_assignExp:
      {
      }
    case A_ifExp:
      {
      }
    case A_whileExp:
      {
      }
    case A_forExp:
      {
      }
    case A_breakExp:
      {
      }
    case A_arrayExp:
      {
      }
  }
  assert(0);
}

void transDec(S_table venv, S_table tenv, A_dec d)
{
  switch(d->kind){
    case A_varDec: 
      {
        struct expty e = transExp(venv, tenv, d->u.var.init);
        S_enter(venv, d->u.var.var, E_VarEntry(e.ty));
      }
    case A_typeDec:
      {
        S_enter(tenv, d->u.type->head->name, transTy(tenv, d->u.type->head->ty));
      }
    case A_functionDec:
      {
        A_fundec f = d->u.function->head;
        Ty_ty resultTy = S_look(tenv, f->result);
        Ty_tyList formalTys = makeFormalTyList(tenv, f->params);
        S_enter(venv, f->name, E_FunEntry(formalTys, resultTy));
        S_beginScope(venv);
        {
          A_fieldList l; Ty_tyList t;
          for(l = f->params, t = formalTys; l; l = l->tail, t = t->tail){
            S_enter(venv, l->head->name, E_VarEntry(t->head));
          }
        }
        transExp(venv, tenv, d->u.function);
        S_endScope(venv);
        break;
      }
  }
}

Ty_ty transTy(S_table tenv, A_ty a)
{
  switch(a->kind){
    case A_nameTy:
      {
      }
    case A_recordTy:
      {
      }
    case A_arrayTy:
      {
      }
  }
}

void SEM_transProg(A_exp exp)
{
  S_table venv = E_base_venv();
  S_table tenv = E_base_tenv();
  transExp(venv, tenv, exp);
}

