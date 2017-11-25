#include <stdio.h>
#include "util.h"
#include "table.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "tree.h"
#include "printtree.h"
#include "frame.h"
#include "translate.h"

//LAB5: you can modify anything you want.

struct Tr_access_ {
	Tr_level level;
	F_access access;
};

struct Tr_accessList_ {
	Tr_access head;
	Tr_accessList tail;	
};

struct Tr_level_ {
	F_frame frame;
	Tr_level parent;
};

typedef struct patchList_ *patchList;
struct patchList_ 
{
	Temp_label *head; 
	patchList tail;
};

struct Cx 
{
	patchList trues; 
	patchList falses; 
	T_stm stm;
};

struct Tr_exp_ {
	enum {Tr_ex, Tr_nx, Tr_cx} kind;
	union {T_exp ex; T_stm nx; struct Cx cx; } u;
};

//global variable
static F_fragList fragList;
static Tr_level outermost;

static Tr_exp Tr_Ex(T_exp ex)
{
  Tr_exp res = checked_malloc(sizeof(*res));
  res->kind = Tr_ex;
  res->u.ex = ex;
  return res;
}

static Tr_exp Tr_Nx(T_stm nx)
{
  Tr_exp res = checked_malloc(sizeof(*res));
  res->kind = Tr_nx;
  res->u.nx = nx;
  return res;
}

static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm);
{
  Tr_exp res = checked_malloc(sizeof(*res));
  res->kind = Tr_cx;
  res->u.cx = cx;
  return res;
}

static T_exp unEx(Tr_exp e)
{
  switch(e->kind){
    case Tr_ex:
      return e->u.ex;
    case Tr_cx:
      {
        Temp_temp r = Temp_newtemp();
        Temp_label t = Temp_newlabel(), f = Temp_newlabel();
        doPatch(e->u.cx.trues, t);
        doPatch(e->u.cx.falses, f);
        return T_Eseq(T_Move(T_Temp(r), T_Const(1)),
                T_Eseq(e->u.cx.stm,
                  T_Eseq(T_Label(f),
                    T_Eseq(T_Move(T_Temp(r), T_Const(0)),
                      T_Eseq(T_Label(t), T_Temp(r))))));
      }
    case Tr_nx:
      return T_Eseq(e->u.nx, T_Const(0));
  }
  assert(0);
}

static T_stm unNx(Tr_exp e)
{
  switch(e->kind){
    case Tr_ex:
      return T_exp(e->u.ex);
    case Tr_cx:
      {
        Temp_label l = Temp_newlabel();
        doPatch(e->u.cx.trues, l);
        doPatch(e->u.cx.falses, l);
        return T_Seq(e->u.cx.stm, T_Label(l));
      }
    case Tr_nx:
      return e->u.nx;
  }
  assert(0);
}

static struct Cx unCx(Tr_exp e)
{
  switch(e->kind){
    case Tr_ex:
      {
        struct Cx cx;
        cx.stm = T_Cjump(T_ne, e->u.ex, T_Const(0), NULL, NULL);
        patchList trues = PatchList(cx.stm->CJUMP.true, NULL);
        patchList falses = PatchList(cx.stm->CJUMP.false, NULL);
        cx.trues = trues;
        cx.falses = falses;
        return cx;
      }
      return; 
    case Tr_cx:
      return e->u.cx;
    case Tr_nx:
      assert(0);
  }
  assert(0);
}

static patchList PatchList(Temp_label *head, patchList tail)
{
	patchList list;

	list = (patchList)checked_malloc(sizeof(struct patchList_));
	list->head = head;
	list->tail = tail;
	return list;
}

void doPatch(patchList tList, Temp_label label)
{
	for(; tList; tList = tList->tail)
		*(tList->head) = label;
}

patchList joinPatch(patchList first, patchList second)
{
	if(!first) return second;
	for(; first->tail; first = first->tail);
	first->tail = second;
	return first;
}

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail)
{
  Tr_accessList a = checked_malloc(sizeof(*a));
  a->head = head;
  a->tail = tail;
  return a;
}

Tr_level Tr_outermost()
{
  if(!outermost){
    outermost = checked_malloc(sizeof(*outermost));
    outermost->frame = NULL;
    outermost->parent = NULL;
  }  
  return l;
}

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals)
{
  Tr_level l = checked_malloc(sizeof(*l));
  l->frame = F_newFrame(name, formals);
  l->parent = parent;
  return l;
}

Tr_accessList Tr_formals(Tr_level level)
{
  return F_formals(level->frame);
}

Tr_access Tr_allocLocal(Tr_level level, bool escape)
{
  Tr_access a = checked_malloc(sizeof(*));
  a->level = level;
  a->access = F_allocLocal(level->frame, escape);
  return a;
}

Tr_exp Tr_simpleVar(Tr_access access, Tr_level level)
{ 
  T_exp framePtr = T_Temp(F_FP());
  //following static link
  for(; level != access->u.level; level = level->parent){
    framePtr = F_Exp(F_formals(level->frame)->head, framePtr);
  }
  return Tr_Ex(F_exp(access->access, framePtr));
}

Tr_exp Tr_fieldVar(Tr_exp base_addr, int offset)
{
  return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(base_addr), T_Const(offset * F_wordSize))));
}

Tr_exp Tr_subscriptVar(Tr_exp base_addr, Tr_exp index)
{
  return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(base_addr), T_Binop(T_mul, unEx(index), T_Const(F_wordSize)))));
}

Tr_exp Tr_nilExp()
{
  return Tr_Ex(T_Const(0));
}

Tr_exp Tr_intExp(int value)
{
  return Tr_Ex(T_Const(value));
}

Tr_exp Tr_stringExp(string stringg)
{
  Temp_label l = Temp_newlabel();
  fragList = F_FragList(F_StringFrag(l, stringg), fragList);
  return Tr_Ex(T_Name(l));
}

Tr_exp Tr_callExp()
{
  return NULL;
}

Tr_exp Tr_opExp(A_oper oper, Tr_exp left, Tr_exp right)
{
  switch(oper){
    case A_plusOp:
      return T_Binop(T_plus, left, right);
    case A_minusOp:
      return T_Binop(T_minus, left, right);
    case A_timesOp:
      return T_Binop(T_mul, left, right);
    case A_divideOp:
      return T_Binop(T_div, left, right);
    case A_eqOp:
      return Tr_ex(unEx(T_Cjump(T_eq, left.u.ex, right.u.ex, NULL, NULL)));
    case A_neqOp:
      return Tr_ex(unEx(T_Cjump(T_ne, left.u.ex, right.u.ex, NULL, NULL)));
    case A_ltOp:
      return Tr_ex(unEx(T_Cjump(T_lt, left.u.ex, right.u.ex, NULL, NULL)));
    case A_leOp:
      return Tr_ex(unEx(T_Cjump(T_le, left.u.ex, right.u.ex, NULL, NULL)));
    case A_gtOp:
      return Tr_ex(unEx(T_Cjump(T_gt, left.u.ex, right.u.ex, NULL, NULL)));
    case A_geOp:
      return Tr_ex(unEx(T_Cjump(T_ge, left.u.ex, right.u.ex, NULL, NULL)));
  }
  assert(0);
}

Tr_seqExp(Tr_exp seq, Tr_exp exp)
{
  return Tr_Ex(T_Eseq(unNx(seq), unEx(exp));
}

Tr_exp Tr_assignExp(Tr_exp var, Tr_exp exp)
{
  return Tr_Nx(T_Move(unEx(var), unEx(exp)));
}

Tr_exp Tr_ifExp(Tr_exp test, Tr_exp then, Tr_exp elsee)
{
  if(elsee){
    Temp_temp r = Temp_newtemp();
    Temp_label t = Temp_newlabel(), f = Temp_newlabel();
    struct Cx cx = unCx(test);
    doPatch(cx->trues, t);
    doPatch(cx->falses, f);
    return Tr_Ex(T_Eseq(T_Move(T_Temp(r), unEx(then)),
                   T_Eseq(cx->stm),
                     T_Eseq(T_Label(f),
                       T_Eseq(T_Move(T_Temp(r), unEx(elsee)),
                         T_Eseq(T_Label(t), T_Temp(r))))));
  }else{
    Temp_label t = Temp_newlabel(), f = Temp_newlabel();
    struct Cx cx = unCx(test);
    doPatch(cx->trues, t);
    doPatch(cx->falses, f);
    return Tr_Nx(T_Seq(cx->stm,
                   T_Seq(T_Label(t), 
                     T_Seq(unNx(then), T_Label(f)))));
  }
}

Tr_exp Tr_whileExp(Tr_exp test, Tr_exp body, Temp_label done)
{
  Temp_label testl = Temp_newlabel(), t = Temp_newlabel();
  struct Cx cx = unCx(test);
  doPatch(cx.trues ,t);
  doPatch(cx.falses, done);
  return T_Seq(T_Label(testl),
           T_Seq(cx.stm,
             T_Seq(T_Label(t),
               T_Seq(unNx(body,
                   T_Seq(T_Jump(T_Name(testl, Temp_LabelList(T_Name(testl, NULL))), T_Label(done))))))));
}

Tr_exp Tr_breakExp(Temp_label done)
{
  return Tr_Nx(T_Jump(T_Name(done), Temp_LabelList(T_Name(done), NULL)));
}

Tr_exp Tr_forExp()
{
  return NULL;
}

Tr_noExp()
{
  return Tr_Ex(T_Const(0));
}

Tr_exp Tr_arrayExp()
{
  return NULL;
}

F_fragList Tr_getResult()
{
  return fragList;
}

