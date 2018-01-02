#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "env.h"
#include "semant.h"
#include "helper.h"
#include "translate.h"

/*Lab5: Your implementation of lab5*/

struct expty
{
  Tr_exp exp;
  Ty_ty ty;
};

static struct expty expTy(Tr_exp exp, Ty_ty ty)
{
  struct expty e;

  e.exp = exp;
  e.ty = ty;

  return e;
}

static Ty_ty actual_ty(Ty_ty ty)
{
  if(ty->kind == Ty_name){
    return actual_ty(ty->u.name.ty);
  }else{
    return ty;
  }
}

static Ty_tyList makeFormalTyList(S_table tenv, A_fieldList params)
{
  A_fieldList fields;
  Ty_tyList tyList = NULL;

  for (fields = params; fields; fields = fields->tail) {
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

static U_boolList makeFormalBoolList(A_fieldList params)
{
  U_boolList boolList = NULL;
  for(; params; params = params->tail){
    boolList = U_BoolList(params->head->escape, boolList);
  }

  U_boolList rlist = NULL;
  for(; boolList; boolList = boolList->tail){
    rlist = U_BoolList(boolList->head, rlist);
  }

  return rlist;
}

static int assertSameType(Ty_ty a, Ty_ty b)
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

struct expty transVar(S_table venv, S_table tenv, A_var v, Tr_level level, Temp_label label)
{
  switch(v->kind){
    case A_simpleVar:
      {
        E_enventry x = S_look(venv, v->u.simple);
        if(x && x->kind == E_varEntry){
          return expTy(Tr_simpleVar(x->u.var.access, level), x->u.var.ty);
        }else{
          EM_error(v->pos, "undefined variable %s", S_name(v->u.simple));
          return expTy(Tr_noExp(), Ty_Void());
        }
      }
    case A_fieldVar:
      {
        struct expty var = transVar(venv, tenv, v->u.field.var, level, label);

        if(var.ty->kind != Ty_record){
          EM_error(v->pos, "not a record type");
          return expTy(Tr_noExp(), Ty_Void());
        }

        int index = 0;
        for(Ty_fieldList fields = var.ty->u.record; fields; fields = fields->tail, index++){
          if(fields->head->name == v->u.field.sym){
            return expTy(Tr_fieldVar(var.exp, index), fields->head->ty);
          }
        }
        EM_error(v->pos, "field %s doesn't exist", S_name(v->u.field.sym));
        return expTy(Tr_noExp(), Ty_Void());
      }
    case A_subscriptVar:
      {
        struct expty var = transVar(venv, tenv, v->u.field.var, level, label);
        struct expty exp = transExp(venv, tenv, v->u.subscript.exp, level, label);

        if(actual_ty(var.ty)->kind != Ty_array){
          EM_error(v->pos, "array type required");
          return expTy(Tr_noExp(), Ty_Void());
        }

        if(exp.ty->kind != Ty_int){
          EM_error(v->pos, "integer required");
          return expTy(Tr_noExp(), Ty_Void());
        }

        return expTy(Tr_subscriptVar(var.exp, exp.exp), var.ty->u.array);
      }
  }
  assert(0);
}

struct expty transExp(S_table venv, S_table tenv, A_exp a, Tr_level level, Temp_label label)
{
  switch(a->kind){
    case A_opExp:
      {
        A_oper oper = a->u.op.oper;
        struct expty left = transExp(venv, tenv, a->u.op.left, level, label);
        struct expty right = transExp(venv, tenv, a->u.op.right, level, label);
        if(oper == A_plusOp || oper == A_minusOp || oper == A_timesOp || oper == A_divideOp){
          if(left.ty->kind != Ty_int){
            EM_error(a->u.op.left->pos, "integer required");
            return expTy(Tr_noExp(), Ty_Void());
          }
          if(right.ty->kind != Ty_int){
            EM_error(a->u.op.right->pos, "integer required");
            return expTy(Tr_noExp(), Ty_Void());
          }
          return expTy(Tr_arithExp(a->u.op.oper, left.exp, right.exp), Ty_Int());
        }else if(oper == A_eqOp || oper == A_neqOp){
          if(!assertSameType(left.ty, right.ty)){
            EM_error(a->u.op.right->pos, "same type required");
            return expTy(Tr_noExp(), Ty_Void());
          }

          switch(left.ty->kind){
            case Ty_int:
            case Ty_array:
            case Ty_name:
            case Ty_record:
            case Ty_nil:
            case Ty_void:
              return expTy(Tr_relExp(a->u.op.oper, left.exp, right.exp), Ty_Int());
            case Ty_string:
              return expTy(Tr_relStrExp(a->u.op.oper, left.exp, right.exp), Ty_Int());
          }
          assert(0);
        }else if(oper == A_ltOp || A_leOp || A_gtOp || A_geOp){
          if(left.ty->kind != Ty_int){
            EM_error(a->u.op.left->pos, "integer required");
            return expTy(Tr_noExp(), Ty_Void());
          }
          if(right.ty->kind != Ty_int){
            EM_error(a->u.op.right->pos, "integer required");
            return expTy(Tr_noExp(), Ty_Void());
          }

          return expTy(Tr_relExp(a->u.op.oper, left.exp, right.exp), Ty_Int());
        } else {
          assert(0);
        }
      }
    case A_letExp:
      {
        struct expty exp;
        Tr_expList eseq = NULL;
        S_beginScope(venv);
        S_beginScope(tenv);

        for(A_decList decs = a->u.let.decs; decs; decs = decs->tail){
          eseq = Tr_ExpList(transDec(venv, tenv, decs->head, level, label), eseq);
        }
        exp = transExp(venv, tenv, a->u.let.body, level, label);
        eseq = Tr_ExpList(exp.exp, eseq);
        S_endScope(tenv);
        S_endScope(venv);

        //ATTENTION: seqs is in reverse direction, the head will be executed last.
        return expTy(Tr_seqExp(eseq), exp.ty);
      }
    case A_varExp:
      {
        return transVar(venv, tenv, a->u.var, level, label);
      }
    case A_nilExp:
      {
        return expTy(Tr_nilExp(), Ty_Nil());
      }
    case A_intExp:
      {
        return expTy(Tr_intExp(a->u.intt), Ty_Int());
      }
    case A_stringExp:
      {
        return expTy(Tr_stringExp(a->u.stringg), Ty_String());
      }
    case A_callExp:
      {
        A_expList args;
        Ty_tyList formals;
        E_enventry x = S_look(venv, a->u.call.func);
        Tr_expList expList = NULL, rlist = NULL;

        if(!x || x->kind != E_funEntry){
          EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
          return expTy(Tr_noExp(), Ty_Void());
        }

        for(args = a->u.call.args, formals = x->u.fun.formals; args && formals; args = args->tail, formals = formals->tail){
          struct expty exp = transExp(venv, tenv, args->head, level, label);
          if(!assertSameType(formals->head, exp.ty)){
            EM_error(args->head->pos, "para type mismatch");
          }
          expList = Tr_ExpList(exp.exp, expList);
        }

        if(args){
          EM_error(a->pos, "too many params in function %s", S_name(a->u.call.func));
        }
        if(formals){
          EM_error(a->pos, "too less params in function %s", S_name(a->u.call.func));
        }

        for(; expList; expList = expList->tail){
          rlist = Tr_ExpList(expList->head, rlist);
        }

        return expTy(Tr_callExp(level, x->u.fun.level, x->u.fun.label, rlist), x->u.fun.result);
      }
    case A_recordExp:
      {
        Ty_ty ty  = actual_ty(S_look(tenv, a->u.record.typ));

        if(!ty){
          EM_error(a->pos, "undefined type %s", S_name(a->u.record.typ));
          return expTy(Tr_noExp(), Ty_Void());
        }

        if(ty->kind != Ty_record){
          EM_error(a->pos, "not a record type");
          return expTy(Tr_noExp(), Ty_Void());
        }

        int size = 0;
        A_efieldList efields;
        Ty_fieldList fields;
        Tr_expList fieldList = NULL, rlist = NULL;
        for(efields = a->u.record.fields, fields = ty->u.record; efields && fields; efields = efields->tail, fields = fields->tail, size++){
          struct expty exp = transExp(venv, tenv, efields->head->exp, level, label);
          if (!(efields->head->name == fields->head->name && assertSameType(fields->head->ty, exp.ty))) {
            EM_error(efields->head->exp->pos, "type mismatch%s", S_name(fields->head->name));
          }
          fieldList = Tr_ExpList(exp.exp, fieldList);
        }

         //ATTENTION: fieldList is in reverse direction, the head will be executed last.
        return expTy(Tr_recordExp(size, fieldList), ty);
      }
    case A_seqExp:
      {
        // one or more exps.
        struct expty exp;
        Tr_expList eseq = NULL;

        for(A_expList exps = a->u.seq; exps && exps->head; exps = exps->tail){
          exp = transExp(venv, tenv, exps->head, level, label);
          eseq = Tr_ExpList(exp.exp, eseq);
        }

        //ATTENTION: seqs is in reverse direction, the head will be executed last.
        return expTy(Tr_seqExp(eseq), exp.ty);
      }
    case A_assignExp:
      {
        struct expty var = transVar(venv, tenv, a->u.assign.var, level, label);
        struct expty exp = transExp(venv, tenv, a->u.assign.exp, level, label);

        if(a->u.assign.var->kind == A_simpleVar){
          E_enventry x = S_look(venv, a->u.assign.var->u.simple);
          if(x->readonly){
            EM_error(a->u.assign.var->pos, "loop variable can't be assigned");
            return expTy(Tr_noExp(), Ty_Void());
          }
        }

        return expTy(Tr_assignExp(var.exp, exp.exp), Ty_Void());
      }
    case A_ifExp:
      {
        struct expty test = transExp(venv, tenv, a->u.iff.test, level, label);
        if(test.ty->kind != Ty_int){
          EM_error(a->u.iff.test->pos, "integer required");
          return expTy(Tr_noExp(), Ty_Void());
        }

        struct expty then = transExp(venv, tenv, a->u.iff.then, level, label);

        if(a->u.iff.elsee){
          struct expty elsee = transExp(venv, tenv, a->u.iff.elsee, level, label);
          if(!assertSameType(then.ty, elsee.ty)){
            EM_error(a->u.iff.elsee->pos, "then exp and else exp type mismatch");
            return expTy(Tr_noExp(), Ty_Void());
          }
          return expTy(Tr_ifExp(test.exp, then.exp, elsee.exp), then.ty);
        }else{
          if(then.ty->kind != Ty_void){
            EM_error(a->u.iff.then->pos, "if-then exp's body must produce no value");
            return expTy(Tr_noExp(), Ty_Void());
          }
          return expTy(Tr_ifExp(test.exp, then.exp, NULL), Ty_Void());
        }
      }
    case A_whileExp:
      {
        struct expty test = transExp(venv, tenv, a->u.whilee.test, level, NULL);
        if(test.ty->kind != Ty_int){
          EM_error(a->u.whilee.test->pos, "integer required");
          return expTy(Tr_noExp(), Ty_Void());
        }

        Temp_label done = Temp_newlabel();
        struct expty body = transExp(venv, tenv, a->u.whilee.body, level, done);
        if(body.ty->kind != Ty_void){
          EM_error(a->u.iff.then->pos, "while body must produce no value");
          return expTy(Tr_noExp(), Ty_Void());
        }
        return expTy(Tr_whileExp(test.exp, body.exp, done), Ty_Void());
      }
    case A_forExp:
      {
        struct expty lo = transExp(venv, tenv, a->u.forr.lo, level, label);
        struct expty hi = transExp(venv, tenv, a->u.forr.hi, level, label);
        Temp_label done = Temp_newlabel();
        if(lo.ty->kind != Ty_int){
          EM_error(a->u.forr.lo->pos, "for exp's range type is not integer");
        }
        if(hi.ty->kind != Ty_int){
          EM_error(a->u.forr.hi->pos, "for exp's range type is not integer");
        }

        S_beginScope(venv);
        Tr_access access = Tr_allocLocal(level, a->u.forr.escape);
        S_enter(venv, a->u.forr.var, E_VarEntry(access, Ty_Int()));
        struct expty body = transExp(venv, tenv, a->u.forr.body, level, done);
        if(body.ty->kind != Ty_void){
          EM_error(a->u.iff.then->pos, "for body must produce no value");
        }
        S_endScope(venv);
        return expTy(Tr_forExp(access, level, lo.exp, hi.exp, body.exp, done), Ty_Void());
      }
    case A_breakExp:
      {
        if(label == NULL) {
          EM_error(a->pos, "break is not inside any loops");
          return expTy(Tr_noExp(), Ty_Void());
        }
        return expTy(Tr_breakExp(label), Ty_Void());
      }
    case A_arrayExp:
      {
        Ty_ty ty = actual_ty(S_look(tenv, a->u.array.typ));
        struct expty size = transExp(venv, tenv, a->u.array.size, level, label);
        struct expty init = transExp(venv, tenv, a->u.array.init, level, label);

        if(!ty){
          EM_error(a->pos, "undefined type %s", S_name(a->u.array.typ));
          return expTy(Tr_noExp(), Ty_Void());
        }

        if(ty->kind != Ty_array){
          EM_error(a->pos, "same type required");
          return expTy(Tr_noExp(), Ty_Void());
        }

        if(size.ty->kind != Ty_int){
          EM_error(a->pos, "integer required");
          return expTy(Tr_noExp(), Ty_Void());
        }

        if(!assertSameType(init.ty, ty->u.array)){
          EM_error(a->pos, "type mismatch");
          return expTy(Tr_noExp(), Ty_Void());
        }

        return expTy(Tr_arrayExp(size.exp, init.exp), ty);
      }
    case A_voidExp:
      {
        return expTy(Tr_noExp(), Ty_Void());
      }
  }
  assert(0);
}

Tr_exp transDec(S_table venv, S_table tenv, A_dec d, Tr_level level, Temp_label label)
{
  switch(d->kind){
    case A_varDec:
      {
        struct expty init;

        init = transExp(venv, tenv, d->u.var.init, level, label);

        if(strcmp("",S_name(d->u.var.typ)) != 0){
          Ty_ty ty = S_look(tenv, d->u.var.typ);
          if(!assertSameType(ty, init.ty)){
            EM_error(d->pos, "type mismatch");
            return Tr_noExp();
          }
        }else{
          if(init.ty->kind == Ty_nil){
            EM_error(d->pos, "init should not be nil without type specified");
            return Tr_noExp();
          }
        }

        Tr_access access = Tr_allocLocal(level, d->u.var.escape);
        S_enter(venv, d->u.var.var, E_VarEntry(access, init.ty));
        return Tr_assignExp(Tr_simpleVar(access, level), init.exp);
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
              break;
            }
          }
        }

        return Tr_noExp();
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
          if(strcmp("", S_name(fundecs->head->result)) == 0){
            resultTy = Ty_Void();
          }else{
            resultTy = S_look(tenv, fundecs->head->result);
          }

          Ty_tyList formalTys = makeFormalTyList(tenv, fundecs->head->params);
          U_boolList formals = makeFormalBoolList(fundecs->head->params);
          Temp_label funLabel = Temp_newlabel();
          Tr_level funLevel = Tr_newLevel(level, funLabel, formals);
          S_enter(venv, fundecs->head->name, E_FunEntry(funLevel, funLabel, formalTys, resultTy));
        }

        for(A_fundecList fundecs = d->u.function; fundecs; fundecs = fundecs->tail){
          S_beginScope(venv);
          E_enventry funentry = S_look(venv, fundecs->head->name);
          Ty_tyList formalTys = funentry->u.fun.formals;
          Ty_ty resultTy = funentry->u.fun.result;
          Tr_accessList accessList = Tr_formals(funentry->u.fun.level);
          for(A_fieldList fields = fundecs->head->params; fields; fields = fields->tail, formalTys = formalTys->tail, accessList = accessList->tail){
            S_enter(venv, fields->head->name, E_VarEntry(accessList->head, formalTys->head));
          }

          exp = transExp(venv, tenv, fundecs->head->body, funentry->u.fun.level, label);
          if(!assertSameType(exp.ty, resultTy)){
            if(resultTy->kind == Ty_void){
              EM_error(fundecs->head->body->pos, "procedure returns value");
            }else{
              EM_error(fundecs->head->body->pos, "type mismatch");
            }
          }
          Tr_procEntryExit(funentry->u.fun.level, exp.exp, accessList);
          S_endScope(venv);
        }
        return Tr_noExp();
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
        Ty_fieldList fieldlist = NULL;

        for(A_fieldList fields = a->u.record; fields; fields = fields->tail){
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

F_fragList SEM_transProg(A_exp exp)
{
  S_table venv = E_base_venv();
  S_table tenv = E_base_tenv();
  struct expty e = transExp(venv, tenv, exp, Tr_outermost(), NULL);
  Tr_procEntryExit(Tr_outermost(), e.exp, NULL);
  return Tr_getResult();
}
