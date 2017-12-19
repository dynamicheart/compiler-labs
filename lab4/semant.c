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

  A_fieldList fields;
  Ty_tyList tyList = NULL;

  for(fields = params; fields; fields = fields->tail) {
    Ty_ty ty = actual_ty(S_look(tenv, fields->head->typ));
    tyList = Ty_TyList(ty, tyList);
  }

  Ty_tyList rlist = NULL;
  while (tyList){
    rlist = Ty_TyList(tyList->head, rlist);
    tyList = tyList->tail;
  }

  return rlist;
}

int assertSameType(Ty_ty a, Ty_ty b)
{
  a = actual_ty(a);
  b = actual_ty(b);
  if (a->kind == Ty_array || b->kind == Ty_array) {
    return a == b;
  } else if (a->kind == Ty_record) {
    return a == b || b->kind == Ty_nil;
  } else if (b->kind == Ty_record) {
    return a == b || a->kind == Ty_nil;
  } else {
    return a->kind == b->kind;
  }
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
          return expTy(NULL, Ty_Void());
        }
      }
    case A_fieldVar:
      {
        struct expty var = transVar(venv, tenv, v->u.field.var);

        if(var.ty->kind != Ty_record){
          EM_error(v->pos, "not a record type");
          return expTy(NULL, Ty_Void());
        }

        for(Ty_fieldList fields = var.ty->u.record; fields; fields = fields->tail){
          if(fields->head->name == v->u.field.sym){
            return expTy(NULL, actual_ty(fields->head->ty));
          }
        }
        EM_error(v->pos, "field %s doesn't exist", S_name(v->u.field.sym));
        return expTy(NULL, Ty_Void());
      }
    case A_subscriptVar:
      {
        struct expty var = transVar(venv, tenv, v->u.field.var);
        struct expty exp = transExp(venv, tenv, v->u.subscript.exp);

        if(var.ty->kind != Ty_array){
          EM_error(v->pos, "array type required");
          return expTy(NULL, Ty_Void());
        }

        if(exp.ty->kind != Ty_int){
          EM_error(v->pos, "integer required");
          return expTy(NULL, Ty_Void());
        }

        return expTy(NULL, actual_ty(var.ty->u.array));
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
        if(oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp){
          if(left.ty->kind != Ty_int){
            EM_error(a->u.op.left->pos, "integer required");
          }
          if(right.ty->kind != Ty_int){
            EM_error(a->u.op.right->pos, "integer required");
          }
        }else if(oper == A_eqOp || oper == A_neqOp){
          if(!assertSameType(left.ty, right.ty)){
            EM_error(a->u.op.right->pos, "same type required");
          }
        }else{
          if(!((left.ty->kind == Ty_int && right.ty->kind == Ty_int) || (left.ty->kind == Ty_string && right.ty->kind == Ty_string))){
            EM_error(a->u.op.right->pos, "same type required");
          }
        }
        return expTy(NULL, Ty_Int());
      }
    case A_letExp:
      {
        struct expty exp;
        S_beginScope(venv);
        S_beginScope(tenv);

        for(A_decList decs = a->u.let.decs; decs; decs = decs->tail){
          transDec(venv, tenv, decs->head);
        }
        exp = transExp(venv, tenv, a->u.let.body);
        S_endScope(tenv);
        S_endScope(venv);
        return exp;
      }
    case A_varExp:
      {
        return transVar(venv, tenv, a->u.var);
      }
    case A_nilExp:
      {
        return expTy(NULL, Ty_Nil());
      }
    case A_intExp:
      {
        return expTy(NULL, Ty_Int());
      }
    case A_stringExp:
      {
        return expTy(NULL, Ty_String());
      }
    case A_callExp:
      {
        A_expList args;
        Ty_tyList formals;
        E_enventry x = S_look(venv, a->u.call.func);

        if(!x || x->kind != E_funEntry){
          EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
          return expTy(NULL, Ty_Void());
        }
        for(args = a->u.call.args, formals = x->u.fun.formals; args && formals; args = args->tail, formals = formals->tail){
          struct expty exp = transExp(venv, tenv, args->head);
          if(!assertSameType(formals->head, exp.ty)){
            EM_error(args->head->pos, "para type mismatch");
          }
        }

        if(args){
          EM_error(a->pos, "too many params in function %s", S_name(a->u.call.func));
        }
        if(formals){
          EM_error(a->pos, "too less params in function %s", S_name(a->u.call.func));
        }

        return expTy(NULL, x->u.fun.result);
      }
    case A_recordExp:
      {
        Ty_ty ty  = actual_ty(S_look(tenv, a->u.record.typ));

        if(!ty){
          EM_error(a->pos, "undefined type %s", S_name(a->u.record.typ));
          return expTy(NULL, Ty_Void());
        }

        if(ty->kind != Ty_record){
          EM_error(a->pos, "not a record type");
          return expTy(NULL, Ty_Void());
        }

        A_efieldList efields;
        Ty_fieldList fields;
        for(efields = a->u.record.fields, fields = ty->u.record; efields && fields; efields = efields->tail, fields = fields->tail){
          struct expty exp = transExp(venv, tenv, efields->head->exp);
          if (!(efields->head->name == fields->head->name && assertSameType(fields->head->ty, exp.ty))) {
            EM_error(efields->head->exp->pos, "type mismatch%s", S_name(fields->head->name));
          }
        }

        return expTy(NULL, ty);
      }
    case A_seqExp:
      {
        struct expty res =  expTy(NULL, Ty_Void());

        for(A_expList exps = a->u.seq; exps && exps->head; exps = exps->tail){
          res = transExp(venv, tenv, exps->head);
        }

        return res;
      }
    case A_assignExp:
      {
        struct expty var = transVar(venv, tenv, a->u.assign.var);
        struct expty exp = transExp(venv, tenv, a->u.assign.exp);

        if(a->u.assign.var->kind == A_simpleVar){
          E_enventry x = S_look(venv, a->u.assign.var->u.simple);
          if(x->readonly){
            EM_error(a->u.assign.var->pos, "loop variable can't be assigned");
            return expTy(NULL, Ty_Void());
          }
        }

        if(!assertSameType(var.ty, exp.ty)){
          EM_error(a->pos, "unmatched assign exp");
        }

        return expTy(NULL, Ty_Void());
      }
    case A_ifExp:
      {
        struct expty test = transExp(venv, tenv, a->u.iff.test);
        if(test.ty->kind != Ty_int){
          EM_error(a->u.iff.test->pos, "integer required");
          return expTy(NULL, Ty_Void());
        }

        struct expty then = transExp(venv, tenv, a->u.iff.then);

        if(a->u.iff.elsee){
          struct expty elsee = transExp(venv, tenv, a->u.iff.elsee);
          if(then.ty->kind != elsee.ty->kind){
            EM_error(a->u.iff.elsee->pos, "then exp and else exp type mismatch");
            return expTy(NULL, Ty_Void());
          }
          return then;
        }else{
          if(then.ty->kind != Ty_void){
            EM_error(a->u.iff.then->pos, "if-then exp's body must produce no value");
            return expTy(NULL, Ty_Void());
          }
          return expTy(NULL, Ty_Void());
        }
      }
    case A_whileExp:
      {
        struct expty test = transExp(venv, tenv, a->u.whilee.test);
        if(test.ty->kind != Ty_int){
          EM_error(a->u.whilee.test->pos, "integer required");
          return expTy(NULL, Ty_Void());
        }

        struct expty body = transExp(venv, tenv, a->u.whilee.body);
        if(body.ty->kind != Ty_void){
          EM_error(a->u.iff.then->pos, "while body must produce no value");
          return expTy(NULL, Ty_Void());
        }
        return expTy(NULL, Ty_Void());
      }
    case A_forExp:
      {
        struct expty lo = transExp(venv, tenv, a->u.forr.lo);
        struct expty hi = transExp(venv, tenv, a->u.forr.hi);
        if(lo.ty->kind != Ty_int){
          EM_error(a->u.forr.lo->pos, "for exp's range type is not integer");
        }
        if(hi.ty->kind != Ty_int){
          EM_error(a->u.forr.hi->pos, "for exp's range type is not integer");
        }

        S_beginScope(venv);
        S_enter(venv, a->u.forr.var, E_ROVarEntry(Ty_Int()));
        struct expty body = transExp(venv, tenv, a->u.forr.body);
        if(body.ty->kind != Ty_void){
          EM_error(a->u.iff.then->pos, "for body must produce no value");
        }
        S_endScope(venv);
        return expTy(NULL, Ty_Void());
      }
    case A_breakExp:
      {
        return expTy(NULL, Ty_Void());
      }
    case A_arrayExp:
      {
        Ty_ty ty = actual_ty(S_look(tenv, a->u.array.typ));
        struct expty size = transExp(venv, tenv, a->u.array.size);
        struct expty init = transExp(venv, tenv, a->u.array.init);

        if(!ty){
          EM_error(a->pos, "undefined type %s", S_name(a->u.array.typ));
          return expTy(NULL, Ty_Void());
        }

        if(ty->kind != Ty_array){
          EM_error(a->pos, "same type required");
          return expTy(NULL, Ty_Void());
        }

        if(size.ty->kind != Ty_int){
          EM_error(a->pos, "integer required");
          return expTy(NULL, Ty_Void());
        }

        if(!assertSameType(init.ty, ty->u.array)){
          EM_error(a->pos, "type mismatch");
          return expTy(NULL, Ty_Void());
        }

        return expTy(NULL, ty);
      }
    case A_voidExp:
      {
        return expTy(NULL, Ty_Void());
      }
  }
  assert(0);
}

void transDec(S_table venv, S_table tenv, A_dec d)
{
  switch(d->kind){
    case A_varDec:
      {
        struct expty e;
        e = transExp(venv, tenv, d->u.var.init);

        if(strcmp("",S_name(d->u.var.typ)) != 0){
          Ty_ty ty = S_look(tenv, d->u.var.typ);
          if(!assertSameType(ty, e.ty)){
            EM_error(d->pos, "type mismatch");
          }

        }else{
          if(e.ty->kind == Ty_nil){
            EM_error(d->pos, "init should not be nil without type specified");
          }
        }

        S_enter(venv, d->u.var.var, E_VarEntry(e.ty));
        return;
      }
    case A_typeDec:
      {
        for(A_nametyList nametys = d->u.type; nametys; nametys = nametys->tail){
          for(A_nametyList scantys = nametys->tail; scantys; scantys = scantys->tail){
            if(strcmp(S_name(scantys->head->name), S_name(nametys->head->name)) == 0){
              EM_error(nametys->head->ty->pos, "two types have the same name");
            }
          }
          S_enter(tenv, nametys->head->name, Ty_Name(nametys->head->name, NULL));
        }

        for(A_nametyList nametys = d->u.type; nametys; nametys = nametys->tail){
          Ty_ty table_ty = S_look(tenv, nametys->head->name);
          Ty_ty real_ty = transTy(tenv, nametys->head->ty);
          table_ty->kind = real_ty->kind;
          table_ty->u = real_ty->u;
        }

        for(A_nametyList nametys = d->u.type; nametys; nametys = nametys->tail){
          Ty_ty actual_ty = S_look(tenv, nametys->head->name);

          while(actual_ty && actual_ty->kind == Ty_name){
            actual_ty = actual_ty->u.name.ty;
            if(actual_ty && actual_ty->kind == Ty_name && actual_ty->u.name.sym == nametys->head->name){
              EM_error(d->pos, "illegal type cycle");
              return;
            }
          }
        }

        return;
      }
    case A_functionDec:
      {
        struct expty exp;

        for(A_fundecList fundecs = d->u.function; fundecs; fundecs = fundecs->tail){
          for(A_fundecList scandecs = fundecs->tail; scandecs; scandecs = scandecs->tail){
            if(strcmp(S_name(scandecs->head->name), S_name(fundecs->head->name)) == 0){
              EM_error(fundecs->head->pos, "two functions have the same name");
            }
          }

          Ty_ty resultTy;
          if(strcmp("",S_name(fundecs->head->result)) == 0){
            resultTy = Ty_Void();
          }else{
            resultTy = S_look(tenv, fundecs->head->result);
          }

          Ty_tyList formalTys = makeFormalTyList(tenv, fundecs->head->params);
          S_enter(venv, fundecs->head->name, E_FunEntry(formalTys, resultTy));
        }

        for(A_fundecList fundecs = d->u.function; fundecs; fundecs = fundecs->tail){
          S_beginScope(venv);
          E_enventry funentry = S_look(venv, fundecs->head->name);
          Ty_tyList formalTys = funentry->u.fun.formals;
          Ty_ty resultTy = funentry->u.fun.result;
          for(A_fieldList fields = fundecs->head->params; fields; fields = fields -> tail, formalTys = formalTys->tail){
            S_enter(venv, fields->head->name, E_VarEntry(formalTys->head));
          }

          exp = transExp(venv, tenv, fundecs->head->body);
          if(!assertSameType(exp.ty, resultTy)){
            if(resultTy->kind == Ty_void){
              EM_error(fundecs->head->body->pos, "procedure returns value");
            }else{
              EM_error(fundecs->head->body->pos, "type mismatch");
            }
          }
          S_endScope(venv);
        }
        return;
      }
  }
  assert(0);
}

Ty_ty transTy(S_table tenv, A_ty a)
{
  switch(a->kind){
    case A_nameTy:
      {
        return Ty_Name(a->u.name, S_look(tenv, a->u.name));
      }
    case A_recordTy:
      {
        A_fieldList fields;
        Ty_fieldList fieldlist = NULL;

        for(fields = a->u.record; fields; fields = fields->tail){
          Ty_ty ty = S_look(tenv, fields->head->typ);
          if(!ty){
            EM_error(fields->head->pos, "undefined type %s", S_name(fields->head->typ));
          }
          fieldlist = Ty_FieldList(Ty_Field(fields->head->name, ty), fieldlist);
        }
        Ty_fieldList rlist = NULL;

        while (fieldlist){
          rlist = Ty_FieldList(fieldlist->head, rlist);
          fieldlist = fieldlist->tail;
        }
        return Ty_Record(rlist);
      }
    case A_arrayTy:
      {
        return Ty_Array(S_look(tenv, a->u.array));
      }
  }
  assert(0);
}

void SEM_transProg(A_exp exp)
{
  S_table venv = E_base_venv();
  S_table tenv = E_base_tenv();
  transExp(venv, tenv, exp);
}
