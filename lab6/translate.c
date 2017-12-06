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

struct Tr_level_ {
	F_frame frame;
	Tr_level parent;
  Tr_accessList formals;
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

static patchList PatchList(Temp_label *head, patchList tail)
{
	patchList list;

	list = (patchList)checked_malloc(sizeof(struct patchList_));
	list->head = head;
	list->tail = tail;
	return list;
}

static void doPatch(patchList tList, Temp_label label)
{
	for(; tList; tList = tList->tail)
		*(tList->head) = label;
}

static patchList joinPatch(patchList first, patchList second)
{
	if(!first) return second;
	for(; first->tail; first = first->tail);
	first->tail = second;
	return first;
}

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

static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm)
{
  Tr_exp res = checked_malloc(sizeof(*res));
  res->kind = Tr_cx;
  res->u.cx.trues = trues;
  res->u.cx.falses = falses;
  res->u.cx.stm = stm;
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
      return T_Exp(e->u.ex);
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
        patchList trues = PatchList(&cx.stm->u.CJUMP.true, NULL);
        patchList falses = PatchList(&cx.stm->u.CJUMP.false, NULL);
        cx.trues = trues;
        cx.falses = falses;
        return cx;
      }
    case Tr_cx:
      return e->u.cx;
    case Tr_nx:
      assert(0);
  }
  assert(0);
}

static Tr_exp staticLink(Tr_level funLevel, Tr_level level)
{
  T_exp addr = T_Temp(F_FP());
  for(; level != funLevel->parent; level = level->parent){
    addr = F_Exp(F_formals(level->frame)->head, addr);
  }

  return Tr_Ex(addr);
}

static Tr_access Tr_Access(Tr_level level, F_access access)
{
  Tr_access traccess = checked_malloc(sizeof(*traccess));
  traccess->level = level;
  traccess->access = access;
  return traccess;
}

static Tr_accessList makeFormalAccessList(Tr_level level)
{
  Tr_accessList alist = NULL, rlist = NULL;
  // discard static link
  F_accessList accessList = F_formals(level->frame)->tail;
  for(; accessList; accessList = accessList->tail){
    alist = Tr_AccessList(Tr_Access(level, accessList->head), alist);
  }

  for(; alist; alist = alist->tail){
    rlist = Tr_AccessList(alist->head, rlist);
  }

  return rlist;
}

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail)
{
  Tr_accessList a = checked_malloc(sizeof(*a));
  a->head = head;
  a->tail = tail;
  return a;
}

Tr_expList Tr_ExpList(Tr_exp head, Tr_expList tail)
{
  Tr_expList e = checked_malloc(sizeof(*e));
  e->head = head;
  e->tail = tail;
  return e;
}

Tr_level Tr_outermost()
{
  if(!outermost){
    outermost = Tr_newLevel(NULL, Temp_newlabel(), NULL);
  }  
  return outermost;
}

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals)
{
  Tr_level l = checked_malloc(sizeof(*l));
  l->frame = F_newFrame(name, U_BoolList(1, formals));
  l->parent = parent;
  l->formals = makeFormalAccessList(l);
  return l;
}

Tr_accessList Tr_formals(Tr_level level)
{
  return level->formals;
}

Tr_access Tr_allocLocal(Tr_level level, bool escape)
{
  Tr_access a = checked_malloc(sizeof(*a));
  a->level = level;
  a->access = F_allocLocal(level->frame, escape);
  return a;
}

Tr_exp Tr_simpleVar(Tr_access access, Tr_level level)
{ 
  T_exp addr = T_Temp(F_FP());
  //following static link
  for(; level != access->level; level = level->parent){
    addr = F_Exp(F_formals(level->frame)->head, addr);
  }
  return Tr_Ex(F_Exp(access->access, addr));
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

Tr_exp Tr_callExp(Tr_level level, Tr_level funLevel, Temp_label label, Tr_expList args)
{
  args = Tr_ExpList(staticLink(funLevel, level), args);
  T_expList expList = NULL, rlist = NULL;
  for(; args; args = args->tail){
    expList = T_ExpList(unEx(args->head), expList);
  }

  for(; expList; expList = expList->tail){
    rlist = T_ExpList(expList->head, rlist);
  }

  return Tr_Ex(T_Call(T_Name(label), rlist));
}

Tr_exp Tr_arithExp(A_oper oper, Tr_exp left, Tr_exp right)
{
  switch(oper){
    case A_plusOp:
      return Tr_Ex(T_Binop(T_plus, unEx(left), unEx(right)));
    case A_minusOp:
      return Tr_Ex(T_Binop(T_minus, unEx(left), unEx(right)));
    case A_timesOp:
      return Tr_Ex(T_Binop(T_mul, unEx(left), unEx(right)));
    case A_divideOp:
      return Tr_Ex(T_Binop(T_div, unEx(left), unEx(right)));
  }
  assert(0);
}

Tr_exp Tr_relExp(A_oper oper, Tr_exp left, Tr_exp right)
{
  T_relOp op;
  switch(oper){
    case A_eqOp:
      op = T_eq;
      break;
    case A_neqOp:
      op = T_ne;
      break;
    case A_ltOp:
      op = T_lt;
      break;
    case A_leOp:
      op = T_le;
      break;
    case A_gtOp:
      op = T_gt;
      break;
    case A_geOp:
      op = T_ge;
      break;
    default:
      assert(0);
  }
  T_stm s = T_Cjump(op, unEx(left), unEx(right), NULL, NULL);
  patchList trues = PatchList(&s->u.CJUMP.true, NULL);
  patchList falses = PatchList(&s->u.CJUMP.false, NULL);
  return Tr_Cx(trues, falses, s);
}

Tr_exp Tr_relStrExp(A_oper oper, Tr_exp left, Tr_exp right)
{
  return Tr_Ex(T_Const(0));
}

Tr_exp Tr_relRefExp(A_oper oper, Tr_exp left, Tr_exp right)
{
  return Tr_Ex(T_Const(0));
}

Tr_exp Tr_recordExp(int n, Tr_expList fields)
{
  Temp_temp r = Temp_newtemp();
  int i = 0;
  T_stm alloc = T_Move(T_Temp(r), F_externalCall(String("malloc"), T_ExpList(T_Const(n * F_wordSize), NULL)));
  T_stm init = T_Move(T_Mem(T_Binop(T_plus, T_Temp(r), T_Const(n * F_wordSize))), unEx(fields->head));
  for(fields = fields->tail; fields; fields = fields->tail){
    init = T_Seq(init, T_Move(T_Mem(T_Binop(T_plus, T_Temp(r), T_Const(n * F_wordSize))), unEx(fields->head)));
  }
  return Tr_Ex(T_Eseq(T_Seq(alloc, init), T_Temp(r)));
}

Tr_exp Tr_seqExp(Tr_expList seq)
{
  T_exp res = unEx(seq->head);
  for(seq = seq->tail; seq; seq = seq->tail){
    res = T_Eseq(T_Exp(unEx(seq->head)), res);
  }
  return Tr_Ex(res);
}

Tr_exp Tr_assignExp(Tr_exp var, Tr_exp exp)
{
  return Tr_Nx(T_Move(unEx(var), unEx(exp)));
}

Tr_exp Tr_ifExp(Tr_exp test, Tr_exp then, Tr_exp elsee)
{
  if(elsee != NULL){
    Temp_temp r = Temp_newtemp();
    Temp_label t = Temp_newlabel(), f = Temp_newlabel(), j = Temp_newlabel();
    struct Cx cx = unCx(test);
    doPatch(cx.trues, t);
    doPatch(cx.falses, f);
    return Tr_Ex(T_Eseq(cx.stm, 
                   T_Eseq(T_Label(t),
                     T_Eseq(T_Move(T_Temp(r), unEx(then)),
                       T_Eseq(T_Jump(T_Name(j), Temp_LabelList(j, NULL)),
                         T_Eseq(T_Label(f),
                           T_Eseq(T_Move(T_Temp(r), unEx(elsee)),
                             T_Eseq(T_Jump(T_Name(j), Temp_LabelList(j, NULL)),
                               T_Eseq(T_Label(j), T_Temp(r))))))))));
  }else{
    Temp_label t = Temp_newlabel(), f = Temp_newlabel();
    struct Cx cx = unCx(test);
    doPatch(cx.trues, t);
    doPatch(cx.falses, f);
    return Tr_Nx(T_Seq(cx.stm,
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
  return Tr_Nx(T_Seq(T_Label(testl),
            T_Seq(cx.stm,
              T_Seq(T_Label(t),
                T_Seq(unNx(body),
                  T_Seq(T_Jump(T_Name(testl), Temp_LabelList(testl, NULL)), T_Label(done)))))));
}

Tr_exp Tr_breakExp(Temp_label done)
{
  return Tr_Nx(T_Jump(T_Name(done), Temp_LabelList(done, NULL)));
}

Tr_exp Tr_forExp(Tr_access access, Tr_level level, Tr_exp lo, Tr_exp hi, Tr_exp body, Temp_label done)
{
  Tr_exp i = Tr_simpleVar(access, level);
  Temp_temp max = Temp_newtemp();
  Temp_label b = Temp_newlabel(), inc = Temp_newlabel();

  return Tr_Nx(T_Seq(T_Move(unEx(i), unEx(lo)),
                 T_Seq(T_Move(T_Temp(max), unEx(hi)),
                   T_Seq(T_Cjump(T_gt, unEx(i), T_Temp(max), done, b), 
                     T_Seq(T_Label(b),
                       T_Seq(unNx(body),
                         T_Seq(T_Cjump(T_eq, unEx(i), T_Temp(max), done, inc),
                           T_Seq(T_Label(inc),
                             T_Seq(T_Move(unEx(i), T_Binop(T_plus, unEx(i), T_Const(1))),
                               T_Seq(T_Jump(T_Name(b), Temp_LabelList(b, NULL)), T_Label(done)))))))))));
}

Tr_exp Tr_arrayExp(Tr_exp size, Tr_exp init)
{
  return Tr_Ex(F_externalCall(String("initArray"),
                T_ExpList(unEx(size), T_ExpList(unEx(init), NULL))));
}

Tr_exp Tr_noExp()
{
  return Tr_Ex(T_Const(0));
}

void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals)
{
  fragList = F_FragList(F_ProcFrag(unNx(body), level->frame), fragList);
}

F_fragList Tr_getResult()
{
  return fragList;
}

