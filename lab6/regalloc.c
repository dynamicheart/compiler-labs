#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "liveness.h"
#include "color.h"
#include "regalloc.h"
#include "table.h"
#include "flowgraph.h"

#define BUF_SIZE 40

static Temp_tempList replaceTemp(Temp_tempList temps, Temp_temp origin, Temp_temp new)
{
	Temp_tempList reverses = NULL;
	for(; temps; temps = temps->tail) {
		if(temps->head == origin) {
			reverses = Temp_TempList(new, reverses);
		} else {
			reverses = Temp_TempList(temps->head, reverses);
		}
	}

	Temp_tempList res = NULL;
	for(; reverses; reverses = reverses->tail) {
		res = Temp_TempList(reverses->head, res);
	}

	return res;
}

static Temp_tempList* getDefs(AS_instr inst) {
  switch (inst->kind) {
    case I_OPER:
      return &inst->u.OPER.dst;
    case I_LABEL:
      return NULL;
    case I_MOVE:
      return &inst->u.MOVE.dst;
    default:
      assert(0);
  }
}

static Temp_tempList* getUses(AS_instr inst) {
  switch (inst->kind) {
  	case I_OPER:
      return &inst->u.OPER.src;
    case I_LABEL:
      return NULL;
    case I_MOVE:
      return &inst->u.MOVE.src;
    default:
      assert(0);
  }
}

static AS_instrList removeRedundantMoves(Temp_map coloring, AS_instrList il)
{
	AS_instrList last_insts = NULL;
	AS_instrList cur_insts = il;
	AS_instrList next_insts;
	while(cur_insts) {
		next_insts = cur_insts->tail;

		if(cur_insts->head->kind == I_MOVE) {
			string temp1 = Temp_look(coloring, cur_insts->head->u.MOVE.src->head);
			string temp2 = Temp_look(coloring, cur_insts->head->u.MOVE.dst->head);
			if(temp1 == temp2) {
				if(last_insts) {
					last_insts->tail = next_insts;
				}else {
					il = next_insts;
				}
			}else {
				last_insts = cur_insts;
			}

			cur_insts = next_insts;
		}else {
			last_insts = cur_insts;
			cur_insts = next_insts;

		}
	}
	return il;
}

static AS_instrList rewriteProgram(F_frame f, AS_instrList il, Temp_tempList spills)
{
	for(; spills; spills = spills->tail) {

		int offset = F_allocSpill(f);

		AS_instrList last_insts = NULL;
		AS_instrList cur_insts = il;
		AS_instrList next_insts;

		while(cur_insts) {
			next_insts = cur_insts->tail;

			if(cur_insts->head->kind == I_LABEL) {
				last_insts = cur_insts;
				cur_insts = next_insts;
				continue;
			}

			Temp_tempList *uses = getUses(cur_insts->head);
			Temp_tempList *defs = getDefs(cur_insts->head);

			Temp_temp t = NULL;
			if(Temp_inTempList(spills->head, *uses)) {
				if(t == NULL) {
          t = Temp_newspill();
        }
				*uses = replaceTemp(*uses, spills->head, t);
				char *a = checked_malloc(BUF_SIZE * sizeof(char));
        sprintf(a, "\nmovl %d(%%ebp), `d0\n", offset);
				AS_instrList new_insts = AS_InstrList(AS_Oper(a, Temp_TempList(t, NULL), NULL, NULL), cur_insts);
				if(last_insts) {
					last_insts->tail = new_insts;
				}else {
					il = new_insts;
				}

			}

			last_insts = cur_insts;

			if(Temp_inTempList(spills->head, *defs)) {
				if(t == NULL) {
          t = Temp_newtemp();
        }
				*defs = replaceTemp(*defs, spills->head, t);
				char *a = checked_malloc(BUF_SIZE * sizeof(char));
        sprintf(a, "\nmovl `s0, %d(%%ebp)\n", offset);
				cur_insts->tail = AS_InstrList(AS_Oper(a, NULL, Temp_TempList(t, NULL), NULL), next_insts);
        last_insts = cur_insts->tail;

			}

			cur_insts = next_insts;
		}

	}
	return il;
}

struct RA_result RA_regAlloc(F_frame f, AS_instrList il) {
	//your code here
	G_graph flow_graph = FG_AssemFlowGraph(il, f);
	struct Live_graph live_graph = Live_liveness(flow_graph);
	Temp_map initial = Temp_layerMap(Temp_empty(), Temp_name());
	Temp_tempList regs = F_registers();

	struct COL_result col_result = COL_color(live_graph, initial, regs);
	if(col_result.spills) {
		il = rewriteProgram(f, il, col_result.spills);
		return RA_regAlloc(f, il);
	}

	struct RA_result ret;
	ret.il = removeRedundantMoves(col_result.coloring, il);
	//ret.il = il;
	ret.coloring = col_result.coloring;
	return ret;
}
