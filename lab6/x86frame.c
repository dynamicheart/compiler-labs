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
	int offset =  F_wordSize * 2; // saved ebp, return address
  for(; formals; formals = formals->tail, offset += F_wordSize){
		alist = F_AccessList(InFrame(offset), alist);
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

static Temp_map tempmap = NULL;
Temp_map F_tempMap(void)
{
	if(tempmap == NULL) {
		tempmap = Temp_empty();
		Temp_enter(tempmap, F_EAX(), "%eax");
		Temp_enter(tempmap, F_EBX(), "%ebx");
		Temp_enter(tempmap, F_ECX(), "%ecx");
		Temp_enter(tempmap, F_EDX(), "%edx");
		Temp_enter(tempmap, F_ESI(), "%esi");
		Temp_enter(tempmap, F_EDI(), "%edi");
		Temp_enter(tempmap, F_ESP(), "%esp");
		Temp_enter(tempmap, F_EBP(), "%ebp");
	}
	return tempmap;
}

static Temp_tempList registers = NULL;
Temp_tempList F_registers(void)
{
	// ebp and esp have special usages
	if(registers == NULL) {
		registers = Temp_TempList(F_EAX(),
									Temp_TempList(F_EBX(),
										Temp_TempList(F_ECX(),
											Temp_TempList(F_EDX(),
												Temp_TempList(F_ESI(),
													Temp_TempList(F_EDI(), NULL))))));
	}
	return registers;
}

Temp_label F_name(F_frame f)
{
  return f->name;
}

F_accessList F_formals(F_frame f)
{
  return f->formals;
}

int F_frameSize(F_frame f)
{
	return f->local_count * F_wordSize;
}

F_access F_allocLocal(F_frame f, bool escape)
{
  if(escape){
		f->local_count++;
    return InFrame(F_wordSize * (- f->local_count));
  }else{
    return InReg(Temp_newtemp());
  }
}

int F_allocSpill(F_frame f)
{
	f->local_count++;
	return F_wordSize * (- f->local_count);
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

static Temp_temp eax = NULL;
Temp_temp F_EAX(void)
{
	if(eax == NULL) {
		eax = Temp_newtemp();
	}
	return eax;
}

static Temp_temp ebx = NULL;
Temp_temp F_EBX(void)
{
	if(ebx == NULL) {
		ebx = Temp_newtemp();
	}
	return ebx;
}

static Temp_temp ecx = NULL;
Temp_temp F_ECX(void)
{
	if(ecx == NULL) {
		ecx = Temp_newtemp();
	}
	return ecx;
}

static Temp_temp edx = NULL;
Temp_temp F_EDX(void)
{
	if(edx == NULL) {
		edx = Temp_newtemp();
	}
	return edx;
}

static Temp_temp esi = NULL;
Temp_temp F_ESI(void)
{
	if(esi == NULL) {
		esi = Temp_newtemp();
	}
	return esi;
}

static Temp_temp edi = NULL;
Temp_temp F_EDI(void)
{
	if(edi == NULL) {
		edi = Temp_newtemp();
	}
	return edi;
}

static Temp_temp esp = NULL;
Temp_temp F_ESP(void)
{
	if(esp == NULL) {
		esp = Temp_newtemp();
	}
	return esp;
}

static Temp_temp ebp = NULL;
Temp_temp F_EBP(void)
{
	if(ebp == NULL) {
		ebp = Temp_newtemp();
	}
	return ebp;
}

Temp_temp F_FP(void)
{
  return F_EBP();
}

Temp_temp F_RV(void)
{
  return F_EAX();
}

static Temp_tempList callersaves = NULL;
Temp_tempList F_callersaves(void)
{
	if(callersaves == NULL) {
		callersaves = Temp_TempList(F_EAX(),
										Temp_TempList(F_ECX(),
											Temp_TempList(F_EDX(), NULL)));
	}
	return callersaves;
}

static Temp_tempList calleesaves = NULL;
Temp_tempList F_calleesaves(void)
{
	if(calleesaves == NULL) {
		calleesaves = Temp_TempList(F_EBX(),
										Temp_TempList(F_ESI(),
											Temp_TempList(F_EDI(), NULL)));
	}
	return calleesaves;
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

T_stm F_procEntryExit1(F_frame frame, T_exp body)
{
	return T_Move(T_Temp(F_RV()), body);
}
