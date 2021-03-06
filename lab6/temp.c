/*
 * temp.c - functions to create and manipulate temporary variables which are
 *          used in the IR tree representation before it has been determined
 *          which variables are to go into registers.
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "table.h"

struct Temp_temp_ {int num; bool spilled;};

int Temp_int(Temp_temp t)
{
	return t->num;
}

string Temp_labelstring(Temp_label s)
{return S_name(s);
}

static int labels = 0;

Temp_label Temp_newlabel(void)
{char buf[100];
 sprintf(buf,"L%d",labels++);
 return Temp_namedlabel(String(buf));
}

/* The label will be created only if it is not found. */
Temp_label Temp_namedlabel(string s)
{return S_Symbol(s);
}

static int temps = 100;

Temp_temp Temp_newtemp(void)
{Temp_temp p = (Temp_temp) checked_malloc(sizeof (*p));
 p->num=temps++;
 p->spilled=FALSE;
 {char r[16];
  sprintf(r, "%d", p->num);
  Temp_enter(Temp_name(), p, String(r));
 }
 return p;
}

Temp_temp Temp_newspill(void)
{Temp_temp p = (Temp_temp) checked_malloc(sizeof (*p));
 p->num=temps++;
 p->spilled=TRUE;
 {char r[16];
  sprintf(r, "%d", p->num);
  Temp_enter(Temp_name(), p, String(r));
 }
 return p;
}

bool Temp_isspill(Temp_temp temp)
{
 return temp->spilled;
}

struct Temp_map_ {TAB_table tab; Temp_map under;};


Temp_map Temp_name(void) {
 static Temp_map m = NULL;
 if (!m) m=Temp_empty();
 return m;
}

Temp_map newMap(TAB_table tab, Temp_map under) {
  Temp_map m = checked_malloc(sizeof(*m));
  m->tab=tab;
  m->under=under;
  return m;
}

Temp_map Temp_empty(void) {
  return newMap(TAB_empty(), NULL);
}

Temp_map Temp_layerMap(Temp_map over, Temp_map under) {
  if (over==NULL)
      return under;
  else return newMap(over->tab, Temp_layerMap(over->under, under));
}

void Temp_enter(Temp_map m, Temp_temp t, string s) {
  assert(m && m->tab);
  TAB_enter(m->tab,t,s);
}

string Temp_look(Temp_map m, Temp_temp t) {
  string s;
  assert(m && m->tab);
  s = TAB_look(m->tab, t);
  if (s) return s;
  else if (m->under) return Temp_look(m->under, t);
  else return NULL;
}

Temp_tempList Temp_TempList(Temp_temp h, Temp_tempList t)
{Temp_tempList p = (Temp_tempList) checked_malloc(sizeof (*p));
 p->head=h; p->tail=t;
 return p;
}

Temp_labelList Temp_LabelList(Temp_label h, Temp_labelList t)
{Temp_labelList p = (Temp_labelList) checked_malloc(sizeof (*p));
 p->head=h; p->tail=t;
 return p;
}

static FILE *outfile;
void showit(Temp_temp t, string r) {
  fprintf(outfile, "t%d -> %s\n", t->num, r);
}

void Temp_dumpMap(FILE *out, Temp_map m) {
  outfile=out;
  TAB_dump(m->tab,(void (*)(void *, void*))showit);
  if (m->under) {
     fprintf(out,"---------\n");
     Temp_dumpMap(out,m->under);
  }
}

Temp_tempList Temp_union(Temp_tempList temps_a, Temp_tempList temps_b) {
	Temp_tempList res = NULL;
	for(Temp_tempList temps1 = temps_a; temps1; temps1 = temps1->tail) {
		res = Temp_TempList(temps1->head, res);
	}

	for(Temp_tempList temps2 = temps_b; temps2; temps2 = temps2->tail) {
		bool found = FALSE;
		for(Temp_tempList temps1 = temps_a; temps1; temps1 = temps1->tail) {
			if(temps1->head == temps2->head) {
				found = TRUE;
				break;
			}
		}
		if(!found) {
			res = Temp_TempList(temps2->head, res);
		}
	}
	return res;
}

Temp_tempList Temp_difference(Temp_tempList temps_a, Temp_tempList temps_b) {
	Temp_tempList res = NULL;
	for(Temp_tempList temps1 = temps_a; temps1; temps1 = temps1->tail) {
		bool found = FALSE;
		for(Temp_tempList temps2 = temps_b; temps2; temps2 = temps2->tail) {
			if(temps1->head == temps2->head) {
				found = TRUE;
				break;
			}
		}
		if(!found) {
			res = Temp_TempList(temps1->head, res);
		}
	}
	return res;
}

bool Temp_equalTempList(Temp_tempList temps_a, Temp_tempList temps_b) {
	for(Temp_tempList temps1 = temps_a; temps1; temps1 = temps1->tail) {
		bool found = FALSE;
		for(Temp_tempList temps2 = temps_b; temps2; temps2 = temps2->tail) {
			if(temps1->head == temps2->head) {
				found = TRUE;
				break;
			}
		}
		if(!found) {
			return FALSE;
		}
	}
	for(Temp_tempList temps2 = temps_b; temps2; temps2 = temps2->tail) {
		bool found = FALSE;
		for(Temp_tempList temps1 = temps_a; temps1; temps1 = temps1->tail) {
			if(temps2->head == temps1->head) {
				found = TRUE;
				break;
			}
		}
		if(!found) {
			return FALSE;
		}
	}
	return TRUE;
}

bool Temp_inTempList(Temp_temp temp, Temp_tempList temps) {
	for(; temps; temps = temps->tail) {
		if(temps->head == temp) {
			return TRUE;
		}
	}
	return FALSE;
}
