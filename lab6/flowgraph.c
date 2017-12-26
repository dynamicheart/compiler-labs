#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "errormsg.h"
#include "table.h"

Temp_tempList FG_def(G_node n) {
	//your code here.
	AS_instr instr = G_nodeInfo(n);
	switch(instr->kind) {
		case I_OPER:
			return instr->u.OPER.dst;
		case I_LABEL:
			return NULL;
		case I_MOVE:
			return instr->u.MOVE.dst;
		default:
			assert(0);
	}
}

Temp_tempList FG_use(G_node n) {
	//your code here.
	AS_instr instr = G_nodeInfo(n);
	switch(instr->kind) {
		case I_OPER:
			return instr->u.OPER.src;
		case I_LABEL:
			return NULL;
		case I_MOVE:
			return instr->u.MOVE.src;
		default:
			assert(0);
	}
}

bool FG_isMove(G_node n) {
	//your code here.
	AS_instr instr = G_nodeInfo(n);
	return instr->kind == I_MOVE;
}

G_graph FG_AssemFlowGraph(AS_instrList il, F_frame f) {
	//your code here.
	G_graph g = G_Graph();
	G_node a = NULL, b = NULL;
	TAB_table label_node_table = TAB_empty();

	for(AS_instrList ilist = il; ilist; ilist = ilist->tail) {
		b = G_Node(g, ilist->head);

		if(a) {
			G_addEdge(a, b);
		}

		if(ilist->head->kind == I_LABEL) {
			TAB_enter(label_node_table, ilist->head->u.LABEL.label, b);
		}

		a = b;
	}

	//add edges between traces
	for(G_nodeList nodes = G_nodes(g); nodes; nodes = nodes->tail) {
		AS_instr inst = G_nodeInfo(nodes->head);
		if(inst->kind == I_OPER && inst->u.OPER.jumps) {
			Temp_labelList ll = inst->u.OPER.jumps->labels;
			for(; ll; ll = ll->tail) {
				G_node successor = TAB_look(label_node_table, ll->head);
				G_addEdge(nodes->head, successor);
			}
		}
	}
	return g;
}
