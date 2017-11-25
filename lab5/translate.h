#ifndef TRANSLATE_H
#define TRANSLATE_H

#include "util.h"
#include "absyn.h"
#include "temp.h"
#include "frame.h"

/* Lab5: your code below */

typedef struct Tr_exp_ *Tr_exp;

typedef struct Tr_access_ *Tr_access;

typedef struct Tr_accessList_ *Tr_accessList;

typedef struct Tr_level_ *Tr_level;

Tr_accessList Tr_AccessList(Tr_access head, Tr_accessList tail);

Tr_level Tr_outermost(void);

Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals);

Tr_accessList Tr_formals(Tr_level level);

Tr_access Tr_allocLocal(Tr_level level, bool escape);

Tr_exp Tr_simpleVar(Tr_access, Tr_level);
Tr_exp Tr_fieldVar(Tr_exp base_addr, int offset);
Tr_exp Tr_subscriptVar(Tr_exp base_addr, Tr_exp index);

Tr_exp Tr_nilExp();
Tr_exp Tr_intExp(int value);
Tr_exp Tr_stringExp(string stringg);
Tr_exp Tr_callExp();
Tr_exp Tr_opExp(A_oper oper, Tr_exp left, Tr_exp right);
Tr_exp Tr_recordExp();
Tr_exp Tr_seqExp(Tr_exp seq, Tr_exp exp);
Tr_exp Tr_assignExp(Tr_exp var, Tr_exp exp);
Tr_exp Tr_ifExp(Tr_exp test, Tr_exp then, Tr_exp elsee);
Tr_exp Tr_whileExp(Tr_exp test, Tr_exp body, Temp_label done);
Tr_exp Tr_breakExp(Temp_label done);
Tr_exp Tr_forExp(Tr_exp lo, Tr_exp hi, Tr_exp body);
Tr_exp Tr_letExp();
Tr_exp Tr_arrayExp();
Tr_exp Tr_noExp();

void Tr_procEntryExit(Tr_level level, Tr_exp body, Tr_accessList formals);

F_fragList Tr_getResult(void);

#endif

