#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "temp.h"
#include "tree.h"
#include "absyn.h"
#include "assem.h"
#include "frame.h"
#include "graph.h"
#include "flowgraph.h"
#include "liveness.h"
#include "table.h"

static void enterLiveMap(G_table t, G_node flowNode, Temp_tempList temps);
static Temp_tempList lookupLiveMap(G_table t, G_node flownode);
static Temp_tempList unionSet(Temp_tempList set1, Temp_tempList set2);
static Temp_tempList differenceSet(Temp_tempList set1, Temp_tempList set2);
static bool equalSet(Temp_tempList set1, Temp_tempList set2);
static G_node getOrCreateNode(G_graph g, Temp_temp temp, TAB_table temp_node_table);

static void enterLiveMap(G_table t, G_node flowNode, Temp_tempList temps) {
	G_enter(t, flowNode, temps);
}

static Temp_tempList lookupLiveMap(G_table t, G_node flownode) {
	return (Temp_tempList) G_look(t, flownode);
}

static Temp_tempList unionSet(Temp_tempList set1, Temp_tempList set2) {
	Temp_tempList res = NULL;
	for(Temp_tempList temps1 = set1; temps1; temps1 = temps1->tail) {
		res = Temp_TempList(temps1->head, res);
	}

	for(Temp_tempList temps2 = set2; temps2; temps2 = temps2->tail) {
		bool found = FALSE;
		for(Temp_tempList temps1 = set1; temps1; temps1 = temps1->tail) {
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

static Temp_tempList differenceSet(Temp_tempList set1, Temp_tempList set2) {
	Temp_tempList res = NULL;
	for(Temp_tempList temps1 = set1; temps1; temps1 = temps1->tail) {
		bool found = FALSE;
		for(Temp_tempList temps2 = set2; temps2; temps2 = temps2->tail) {
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

static bool equalSet(Temp_tempList set1, Temp_tempList set2) {
	for(Temp_tempList temps1 = set1; temps1; temps1 = temps1->tail) {
		bool found = FALSE;
		for(Temp_tempList temps2 = set2; temps2; temps2 = temps2->tail) {
			if(temps1->head == temps2->head) {
				found = TRUE;
				break;
			}
		}
		if(!found) {
			return FALSE;
		}
	}
	for(Temp_tempList temps2 = set2; temps2; temps2 = temps2->tail) {
		bool found = FALSE;
		for(Temp_tempList temps1 = set1; temps1; temps1 = temps1->tail) {
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

static G_node getOrCreateNode(G_graph g, Temp_temp temp, TAB_table temp_node_table) {
	G_node node = TAB_look(temp_node_table, temp);
	if(!node) {
		node = G_Node(g, temp);
		TAB_enter(temp_node_table, temp, node);
	}
	return node;
}

static void connect(G_graph ig, Temp_temp temp1, Temp_temp temp2, TAB_table temp_node_table) {
	if(temp1 == temp2 || temp1 == F_FP() || temp2 == F_FP()) return;

	G_node a = getOrCreateNode(ig, temp1, temp_node_table);
	G_node b = getOrCreateNode(ig, temp2, temp_node_table);

	G_addEdge(a, b);
	G_addEdge(b, a);
}

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail) {
	Live_moveList lm = (Live_moveList) checked_malloc(sizeof(*lm));
	lm->src = src;
	lm->dst = dst;
	lm->tail = tail;
	return lm;
}

Temp_temp Live_gtemp(G_node n) {
	//your code here.
	return G_nodeInfo(n);
}

// void* show(G_node node, Temp_tempList sets){
// 	for(;sets; sets = sets->tail) {
// 		printf("t%d ", Temp_int(sets->head));
// 	}
// 	printf("\n");
// }

struct Live_graph Live_liveness(G_graph flow) {
	//your code here.
	struct Live_graph lg;
	lg.graph = G_Graph();
	lg.moves = NULL;

	// calculate the in/out set and begin liveness analysis
	G_table in_set_table = G_empty();
	G_table out_set_table = G_empty();
	bool has_change = TRUE;

	while(has_change) {
		has_change = FALSE;
		for(G_nodeList flownodes = G_nodes(flow); flownodes; flownodes = flownodes->tail) {
			Temp_tempList old_in_set = lookupLiveMap(in_set_table, flownodes->head);
			Temp_tempList old_out_set = lookupLiveMap(out_set_table, flownodes->head);
			Temp_tempList use_set = FG_use(flownodes->head);
			Temp_tempList def_set = FG_def(flownodes->head);

			Temp_tempList new_in_set = unionSet(use_set, differenceSet(old_out_set, def_set));
			Temp_tempList new_out_set = NULL;

			for(G_nodeList nodes = G_succ(flownodes->head); nodes; nodes = nodes->tail) {
				new_out_set = unionSet(new_out_set, lookupLiveMap(in_set_table, nodes->head));
			}

			if(!equalSet(old_in_set, new_in_set)) {
				has_change = TRUE;
				enterLiveMap(in_set_table, flownodes->head, new_in_set);
			}

			if(!equalSet(old_out_set, new_out_set)) {
				has_change = TRUE;
				enterLiveMap(out_set_table, flownodes->head, new_out_set);
			}
		}
	}
	// TAB_dump(in_set_table, show);
	// printf("========================\n");
	// TAB_dump(out_set_table, show);
	// printf("========================\n");


	// construct interference graph
	TAB_table temp_node_table = TAB_empty();
	for(Temp_tempList temps1 = F_registers(); temps1; temps1 = temps1->tail) {
		for(Temp_tempList temps2 = F_registers(); temps2; temps2 = temps2->tail) {
			connect(lg.graph, temps1->head, temps2->head, temp_node_table);
		}
	}

	for(G_nodeList flownodes = G_nodes(flow); flownodes; flownodes = flownodes->tail) {
		Temp_tempList liveouts = lookupLiveMap(out_set_table, flownodes->head);
		if(FG_isMove(flownodes->head)) {
			liveouts = differenceSet(liveouts, FG_use(flownodes->head));
			for(Temp_tempList defs = FG_def(flownodes->head); defs; defs = defs->tail) {
				for(Temp_tempList uses = FG_use(flownodes->head); uses; uses = uses->tail) {
					if(uses->head != F_FP() && defs->head != F_FP()) {
						lg.moves = Live_MoveList(getOrCreateNode(lg.graph, uses->head, temp_node_table),
																			getOrCreateNode(lg.graph, defs->head, temp_node_table),
																			lg.moves);
					}
        }
      }
		}

		for(Temp_tempList defs = FG_def(flownodes->head); defs; defs = defs->tail) {
			for(; liveouts; liveouts = liveouts->tail) {
				connect(lg.graph, defs->head, liveouts->head, temp_node_table);
			}
		}
	}

	return lg;
}
