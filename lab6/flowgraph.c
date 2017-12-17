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
	G_table t = G_empty();
	G_node n1 = NULL, n2;
	G_nodelist nodes;
	AS_instrList ilist;
	AS_instr inst;
	TAB_table label_node_maps = TAB_empty();

	for(ilist = il; iList; ilist = ilist->tail) {
		n2 = G_Node(g, ilist->head);

		//not knowing whether there is a edge between neibourgh traces
		if(n1 && ilist->head->kind != I_LABEL) {
			G_addEdge(n1, n2);
		}

		if(ilist->head->kind == I_LABEL) {
			TAB_enter(label_node_maps, ilist->head->u.LABEL.label, n2);
		}

		n1 = n2;
	}

	//add edges between traces
	for(nodes = G_nodes(g); nodes; nodes = nodes->tail) {
		inst = G_nodeInfo(nodes->head);
		if(inst->kind == I_OPER) {
			Temp_labelList ll = inst->u.OPER.jumps->labels;
			for(; ll; ll = ll->tail) {
				G_addEdge(nodes->head, TAB_look(label_node_maps, ll->head));
			}
		}
	}
	return g;
}
