#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"
#include "tree.h"
#include "frame.h"

/*Lab5: Your implementation here.*/

//varibales
struct F_access_ {
	enum {inFrame, inReg} kind;
	union {
		int offset; //inFrame
		Temp_temp reg; //inReg
	} u;
};

const int F_wordSize = 4;

struct F_frame_ {
  Temp_label name;
  F_accessList formals;
  int local_count;
};

F_frag F_StringFrag(Temp_label label, string str)
{
  F_frag string_frag = checked_malloc(sizeof(*string_frag));
  string_frag->kind = F_stringFrag;
  string_frag->u.stringg.label = label;
  string_frag->u.stringg.str = str;
  return string_frag;
}

F_frag F_ProcFrag(T_stm body, F_frame frame)
{
  F_frag proc_frag = checked_malloc(sizeof(*proc_frag));
  proc_frag->kind = F_procFrag;
  proc_frag->u.proc.body = body;
  proc_frag->u.proc.frame = frame;
  return proc_frag;
}

F_fragList F_FragList(F_frag head, F_fragList tail)
{
  F_fragList f = checked_malloc(sizeof(*f));
  f->head = head;
  f->tail = tail;
  return f;
}

static F_access InFrame(int offset)
{
  F_access acc = checked_malloc(sizeof(*acc));
  acc->kind = inFrame;
  acc->u.offset = offset;
  return acc;
}

static F_access InReg(Temp_temp reg)
{
  F_access acc = checked_malloc(sizeof(*acc));
  acc->kind = inReg;
  acc->u.reg = reg;
  return acc;
}

static F_accessList makeFormalAccessList(F_frame f, U_boolList formals)
{
  F_accessList alist = NULL, rlist = NULL;
  int i = 0;
  for(; formals; formals = formals->tail, i++){
    alist = F_AccessList(InFrame((1 + i) * F_wordSize), alist);
  }

  for(; alist; alist = alist->tail){
    rlist = F_AccessList(alist->head, rlist);
  }

  return rlist;
}

F_accessList F_AccessList(F_access head, F_accessList tail){
  F_accessList a = checked_malloc(sizeof(*a));
  a->head = head;
  a->tail = tail;
  return a;
}

Temp_label F_name(F_frame f)
{
  return f->name;
}

F_accessList F_formals(F_frame f)
{
  return f->formals;
}

F_access F_allocLocal(F_frame f, bool escape)
{
  f->local_count++;
  if(escape){
    return InFrame(F_wordSize * (- f->local_count));
  }else{
    return InReg(Temp_newtemp());
  }
}

T_exp F_Exp(F_access acc, T_exp framePtr)
{
  switch(acc->kind){
    case inFrame:
      return T_Mem(T_Binop(T_plus, framePtr, T_Const(acc->u.offset)));;
    case inReg:
      return T_Temp(acc->u.reg);
  }
  assert(0);
}

Temp_temp F_FP(void)
{
  return Temp_newtemp();
}

Temp_temp F_RV(void)
{
  return Temp_newtemp();
}

F_frame F_newFrame(Temp_label name, U_boolList formals)
{
  F_frame f = checked_malloc(sizeof(*f));
  f->name = name;
  f->formals = makeFormalAccessList(f, formals);
  f->local_count = 0;
  return f;
}

T_exp F_externalCall(string s, T_expList args)
{
  return T_Call(T_Name(Temp_namedlabel(s)), args);
}

T_stm F_procEntryExit1(F_frame frame, T_stm stm)
{
  return stm;
}

