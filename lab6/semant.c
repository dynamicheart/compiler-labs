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
  A_fieldList field;
  Ty_tyList tyList = NULL;
  
  for (field = params; field; field = field->tail) {
    Ty_ty ty = actual_ty(S_look(tenv, field->head->typ));
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
  if (a->kind == Ty_array) {
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
          return expTy(Tr_noExp(), Ty_Int());
        }
      }
    case A_fieldVar:
      {
        struct expty var = transVar(venv, tenv, v->u.field.var, level, label);

        Ty_fieldList f;
        int offset = 0;

        if(var.ty->kind != Ty_record){
          EM_error(v->pos, "not a record type");
          return expTy(Tr_noExp(), Ty_Int());
        }

        for(f = var.ty->u.record; f; f = f->tail, offset++){
          if(f->head->name == v->u.field.sym){
            return expTy(Tr_fieldVar(var.exp, offset), f->head->ty);
          }
        }
        EM_error(v->pos, "field %s doesn't exist", S_name(v->u.field.sym));
        return expTy(Tr_noExp(), Ty_Int());
      }
    case A_subscriptVar:
      {
        struct expty var = transVar(venv, tenv, v->u.field.var, level, label);
        struct expty exp = transExp(venv, tenv, v->u.subscript.exp, level, label);

        if(actual_ty(var.ty)->kind != Ty_array){
          EM_error(v->pos, "array type required");
          return expTy(Tr_noExp(), Ty_Int());
        }

        if(exp.ty->kind != Ty_int){
          EM_error(v->pos, "integer required");
          return expTy(Tr_noExp(), Ty_Int());
        }

        return expTy(Tr_subscriptVar(var.exp, exp.exp), actual_ty(var.ty->u.array));
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
          }
          if(right.ty->kind != Ty_int){
            EM_error(a->u.op.right->pos, "integer required");
          }
          return expTy(Tr_arithExp(a->u.op.oper, left.exp, right.exp), Ty_Int());
        }else if(oper == A_eqOp || oper == A_neqOp){
          if(!assertSameType(left.ty, right.ty)){
            EM_error(a->pos, "same type required");
          }

          switch(left.ty->kind){
            case Ty_int:
              return expTy(Tr_relExp(a->u.op.oper, left.exp, right.exp), Ty_Int());
            default:
              return expTy(Tr_relRefExp(a->u.op.oper, left.exp, right.exp), Ty_Int());
          }
          assert(0);
        }else{
          if(!((left.ty->kind == Ty_int && right.ty->kind == Ty_int) || (left.ty->kind == Ty_string && right.ty->kind == Ty_string))){
            EM_error(a->pos, "same type required");
          }
          switch(left.ty->kind){
            case Ty_int:
              return expTy(Tr_relExp(a->u.op.oper, left.exp, right.exp), Ty_Int());
          }
          assert(0);
        }
      }
    case A_letExp:
      {
        struct expty exp;
        A_decList d;
        Tr_expList eseq = NULL;
        S_beginScope(venv);
        S_beginScope(tenv);
        
        for(d = a->u.let.decs; d; d = d->tail){
          eseq = Tr_ExpList(transDec(venv, tenv, d->head, level, label), eseq);
        }
        exp = transExp(venv, tenv, a->u.let.body, level, label);
        eseq = Tr_ExpList(exp.exp, eseq);
        S_endScope(tenv);
        S_endScope(venv);
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
        A_expList arg;
        Ty_tyList formal;
        E_enventry x = S_look(venv, a->u.call.func);
        Tr_expList expList = NULL, rlist = NULL;
       
        if(!x || x->kind != E_funEntry){
          EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
          return expTy(Tr_noExp(), Ty_Int());
        }

        for(arg = a->u.call.args, formal = x->u.fun.formals; arg && formal; arg = arg->tail, formal = formal->tail){
          struct expty exp = transExp(venv, tenv, arg->head, level, label);
          if(!assertSameType(formal->head, exp.ty)){
            EM_error(arg->head->pos, "para type mismatch");
          }
          expList = Tr_ExpList(exp.exp, expList);
        }

        if(arg){
          EM_error(a->pos, "too many params in function %s", S_name(a->u.call.func));
        }
        if(formal){
          EM_error(a->pos, "too less params in function %s", S_name(a->u.call.func));
        }

        for(; expList; expList = expList->tail){
          rlist = Tr_ExpList(expList->head, rlist);
        }

        return expTy(Tr_callExp(level, x->u.fun.level, x->u.fun.label, rlist), x->u.fun.result ? x->u.fun.result : Ty_Void());
      }
    case A_recordExp:
      {
        Ty_ty ty  = actual_ty(S_look(tenv, a->u.record.typ));

        if(!ty){
          EM_error(a->pos, "undefined type %s", S_name(a->u.record.typ));
          return expTy(Tr_noExp(), Ty_Int());
        }

        if(ty->kind != Ty_record){
          EM_error(a->pos, "not a record type");
          return expTy(Tr_noExp(), Ty_Int());
        }

        A_efieldList efield;
        Ty_fieldList field;
        int n = 0;
        Tr_expList flist = NULL, rlist = NULL;
        for(efield = a->u.record.fields, field = ty->u.record; efield && field; efield = efield->tail, field = field->tail, n++){
          struct expty exp = transExp(venv, tenv, efield->head->exp, level, label);
          if (!(efield->head->name == field->head->name && assertSameType(field->head->ty, exp.ty))) {
            EM_error(efield->head->exp->pos, "type mismatch%s", S_name(field->head->name));
          }
          flist = Tr_ExpList(exp.exp, flist);
        }

        for(; flist; flist = flist->tail){
          rlist = Tr_ExpList(flist->head, rlist);
        }

        return expTy(Tr_recordExp(n, rlist), ty);
      }
    case A_seqExp:
      { 
        A_expList e;
        struct expty exp = expTy(Tr_noExp(), Ty_Void());
        Tr_expList eseq = NULL;

        for(e = a->u.seq; e && e->head; e = e->tail){
          exp = transExp(venv, tenv, e->head, level, label);
          eseq = Tr_ExpList(exp.exp, eseq);
        }

        if(eseq == NULL){
          eseq = Tr_ExpList(exp.exp, eseq);
        }

        return expTy(Tr_seqExp(eseq), exp.ty);
      }
    case A_assignExp:
      {
        struct expty var = transVar(venv, tenv, a->u.assign.var, level, label);
        struct expty exp = transExp(venv, tenv, a->u.assign.exp, level, label);

        if(a->u.assign.var->kind == A_simpleVar){
          E_enventry x = S_look(venv, a->u.assign.var->u.simple);
          if(x->readonly){
            EM_error(a->pos, "loop variable can't be assigned");
            return expTy(Tr_noExp(), Ty_Int());
          }
        }

        return expTy(Tr_assignExp(var.exp, exp.exp), Ty_Void());
      }
    case A_ifExp:
      {
        struct expty test = transExp(venv, tenv, a->u.iff.test, level, label);
        if(test.ty->kind != Ty_int){
          EM_error(a->u.iff.test->pos, "integer required");
          return expTy(Tr_noExp(), Ty_Int());
        }

        struct expty then = transExp(venv, tenv, a->u.iff.then, level, label);

        if(a->u.iff.elsee){
          struct expty elsee = transExp(venv, tenv, a->u.iff.elsee, level, label);
          if(!assertSameType(then.ty, elsee.ty)){
            EM_error(a->u.iff.elsee->pos, "then exp and else exp type mismatch");
            return expTy(Tr_noExp(), Ty_Int());
          }
          return expTy(Tr_ifExp(test.exp, then.exp, elsee.exp), then.ty);
        }else{
          if(then.ty->kind != Ty_void){
            EM_error(a->u.iff.then->pos, "if-then exp's body must produce no value");
            return expTy(Tr_noExp(), Ty_Int());
          }
          return expTy(Tr_ifExp(test.exp, then.exp, NULL), Ty_Void());
        }
      }
    case A_whileExp:
      {
        struct expty test = transExp(venv, tenv, a->u.whilee.test, level, NULL);
        if(test.ty->kind != Ty_int){
          EM_error(a->u.whilee.test->pos, "integer required");
          return expTy(Tr_noExp(), Ty_Int());
        }

        Temp_label done = Temp_newlabel();
        struct expty body = transExp(venv, tenv, a->u.whilee.body, level, done);
        if(body.ty->kind != Ty_void){
          EM_error(a->u.iff.then->pos, "while body must produce no value");
          return expTy(Tr_noExp(), Ty_Int());
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
        return expTy(Tr_breakExp(label), Ty_Void());
      }
    case A_arrayExp:
      {
        Ty_ty ty = actual_ty(S_look(tenv, a->u.array.typ));
        struct expty size = transExp(venv, tenv, a->u.array.size, level, label);
        struct expty init = transExp(venv, tenv, a->u.array.init, level, label);

        if(!ty){
          EM_error(a->pos, "undefined type %s", S_name(a->u.array.typ));
          return expTy(Tr_noExp(), Ty_Int());
        }

        if(ty->kind != Ty_array){
          EM_error(a->pos, "same type required");
          return expTy(Tr_noExp(), Ty_Int());
        }

        if(size.ty->kind != Ty_int){
          EM_error(a->pos, "integer required");
          return expTy(Tr_noExp(), Ty_Int());
        }

        if(!assertSameType(init.ty, ty->u.array)){
          EM_error(a->pos, "type mismatch 1");
          return expTy(Tr_noExp(), Ty_Int());
        }

        return expTy(Tr_arrayExp(size.exp, init.exp), ty);
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
        Tr_access access;

        if(d->u.var.init){
          init = transExp(venv, tenv, d->u.var.init, level, label);
        }else{
          init = expTy(Tr_nilExp(), Ty_Void());
        }
       
        if(strcmp("",S_name(d->u.var.typ)) != 0){
          Ty_ty ty = actual_ty(S_look(tenv, d->u.var.typ));
          if(!assertSameType(ty, init.ty)){
            EM_error(d->pos, "type mismatch 2");
          }
        
        }else{
          if(init.ty->kind == Ty_nil){
            EM_error(d->pos, "init should not be nil without type specified");
          }
        }
        
        access = Tr_allocLocal(level, d->u.var.escape);
        S_enter(venv, d->u.var.var, E_VarEntry(access, init.ty));
        return Tr_assignExp(Tr_simpleVar(access, level), init.exp);
      }
    case A_typeDec:
      {
        A_nametyList namety;

        for(namety = d->u.type; namety; namety = namety->tail){
          S_enter(tenv, namety->head->name, Ty_Name(namety->head->name, NULL));
        }

        for(namety = d->u.type; namety; namety = namety->tail){
          Ty_ty ty = transTy(tenv, namety->head->ty);

          Ty_ty nameTy = S_look(tenv, namety->head->name);
          nameTy->u.name.ty = ty;
        }

        return Tr_noExp();
      }
    case A_functionDec:
      {
        A_fundecList f, scan_f;
        A_fieldList field;
        Ty_ty resultTy;
        Ty_tyList formalTys, formalTy;
        E_enventry f_entry;
        struct expty exp;
        U_boolList formals;
        Temp_label funLabel;
        Tr_level funLevel;
        Tr_accessList accessList;

        for(f = d->u.function; f; f = f->tail){
          for(scan_f = f->tail; scan_f; scan_f = scan_f->tail){
            if(strcmp(S_name(scan_f->head->name), S_name(f->head->name)) == 0){
              EM_error(d->pos, "two functions have the same name");
            }
          }
          if(strcmp("", S_name(f->head->result)) == 0){
            resultTy = Ty_Void();
          }else{
            resultTy = S_look(tenv, f->head->result);
          }

          formalTys = makeFormalTyList(tenv, f->head->params);
          formals = makeFormalBoolList(f->head->params);
          funLabel = Temp_newlabel();
          funLevel = Tr_newLevel(level, funLabel, formals);
          S_enter(venv, f->head->name, E_FunEntry(funLevel, funLabel, formalTys, resultTy));
        }

        for(f = d->u.function; f; f = f->tail){
          S_beginScope(venv);
          f_entry = S_look(venv, f->head->name);
          formalTy = f_entry->u.fun.formals;
          resultTy = f_entry->u.fun.result;
          accessList = Tr_formals(f_entry->u.fun.level);
          for(field = f->head->params; field; field = field->tail, formalTy = formalTy->tail, accessList = accessList->tail){
            S_enter(venv, field->head->name, E_VarEntry(accessList->head, formalTy->head));
          }
          
          exp = transExp(venv, tenv, f->head->body, f_entry->u.fun.level, label);
          if(!assertSameType(exp.ty, resultTy)){
            if(resultTy->kind == Ty_void){
              EM_error(f->head->body->pos, "procedure returns value");
            }else{
              EM_error(f->head->body->pos, "type mismatch 3");
            }
          }
          Tr_procEntryExit(f_entry->u.fun.level, exp.exp, accessList);
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
        A_fieldList a_field;
        Ty_fieldList fieldlist = NULL;

        for(a_field = a->u.record; a_field; a_field = a_field->tail){
          Ty_ty ty = S_look(tenv, a_field->head->typ);
          if(!ty){
            EM_error(a_field->head->pos, "undefined type %s", S_name(a_field->head->typ));
          }
          fieldlist = Ty_FieldList(Ty_Field(a_field->head->name, ty), fieldlist);
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

