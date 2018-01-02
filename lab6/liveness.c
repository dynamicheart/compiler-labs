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

static void enterLiveMap(G_table t, G_node flowNode, Temp_tempList temps) {
	G_enter(t, flowNode, temps);
}

static Temp_tempList lookupLiveMap(G_table t, G_node flownode) {
	return (Temp_tempList) G_look(t, flownode);
}

static G_node getOrCreateNode(G_graph g, Temp_temp temp, TAB_table temp_node_table, G_table priorities) {
	G_node node = TAB_look(temp_node_table, temp);
	if(!node) {
		node = G_Node(g, temp);
		TAB_enter(temp_node_table, temp, node);

		int *priority = checked_malloc(sizeof(int));
		*priority = 0;
		G_enter(priorities, node, priority);
	}
	return node;
}

static void addEdge(G_graph ig, Temp_temp temp1, Temp_temp temp2, TAB_table temp_node_table, G_table priorities) {
	if(temp1 == temp2 || temp1 == F_FP() || temp2 == F_FP()) return;

	G_node a = getOrCreateNode(ig, temp1, temp_node_table, priorities);
	G_node b = getOrCreateNode(ig, temp2, temp_node_table, priorities);

	int *priority = G_look(priorities, a);
	*priority = *priority + 1;
	priority = G_look(priorities, b);
	*priority = *priority + 1;

	if(!G_isAdj(a, b)){
		G_addAdj(a, b);

		if(!Temp_inTempList(temp1, F_registers())) {
			G_addEdge(a, b);
		}
		if(!Temp_inTempList(temp2, F_registers())) {
			G_addEdge(b, a);
		}
	}
}

static void increasePriority(G_table priorities, G_node node) {
	int *priority = G_look(priorities, node);
	*priority = *priority + 1;
}

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail) {
	Live_moveList lm = (Live_moveList) checked_malloc(sizeof(*lm));
	lm->src = src;
	lm->dst = dst;
	lm->tail = tail;
	return lm;
}

Live_moveList Live_union(Live_moveList moves_a, Live_moveList moves_b) {
	Live_moveList res = NULL;
	for(Live_moveList moves1 = moves_a; moves1; moves1 = moves1->tail) {
		res = Live_MoveList(moves1->src, moves1->dst, res);
	}

	for(Live_moveList moves2 = moves_b; moves2; moves2 = moves2->tail) {
		bool found = FALSE;
		for(Live_moveList moves1 = moves_a; moves1; moves1 = moves1->tail) {
			if(moves1->src == moves2->src && moves1->dst == moves2->dst) {
				found = TRUE;
				break;
			}
		}
		if(!found) {
			res = Live_MoveList(moves2->src, moves2->dst, res);
		}
	}
	return res;
}

Live_moveList Live_difference(Live_moveList moves_a, Live_moveList moves_b)
{
	Live_moveList res = NULL;
	for(Live_moveList moves1 = moves_a; moves1; moves1 = moves1->tail) {
		bool found = FALSE;
		for(Live_moveList moves2 = moves_b; moves2; moves2 = moves2->tail) {
			if(moves1->src == moves2->src && moves1->dst == moves2->dst) {
				found = TRUE;
				break;
			}
		}
		if(!found) {
			res = Live_MoveList(moves1->src, moves1->dst, res);
		}
	}
	return res;
}

bool Live_inMoveList(Live_moveList moves, G_node src, G_node dst)
{
	for(; moves; moves = moves->tail) {
		if(moves->src == src && moves->dst == dst) {
			return TRUE;
		}
	}
	return FALSE;
}

Temp_temp Live_gtemp(G_node n) {
	//your code here.
	return G_nodeInfo(n);
}

struct Live_graph Live_liveness(G_graph flow) {
	//your code here.
	struct Live_graph lg;
	lg.graph = G_Graph();
	lg.moves = NULL;
	lg.priorities = G_empty();
	lg.precolored = NULL;

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

			Temp_tempList new_in_set = Temp_union(use_set, Temp_difference(old_out_set, def_set));
			Temp_tempList new_out_set = NULL;

			for(G_nodeList nodes = G_succ(flownodes->head); nodes; nodes = nodes->tail) {
				new_out_set = Temp_union(new_out_set, lookupLiveMap(in_set_table, nodes->head));
			}

			if(!Temp_equalTempList(old_in_set, new_in_set)) {
				has_change = TRUE;
				enterLiveMap(in_set_table, flownodes->head, new_in_set);
			}

			if(!Temp_equalTempList(old_out_set, new_out_set)) {
				has_change = TRUE;
				enterLiveMap(out_set_table, flownodes->head, new_out_set);
			}
		}
	}

	// construct interference graph
	TAB_table temp_node_table = TAB_empty();
	for(Temp_tempList temps1 = F_registers(); temps1; temps1 = temps1->tail) {
		for(Temp_tempList temps2 = F_registers(); temps2; temps2 = temps2->tail) {
			addEdge(lg.graph, temps1->head, temps2->head, temp_node_table, lg.priorities);
		}
		lg.precolored = G_NodeList(getOrCreateNode(lg.graph, temps1->head, temp_node_table, lg.priorities), lg.precolored);

	}

	for(G_nodeList flownodes = G_nodes(flow); flownodes; flownodes = flownodes->tail) {
		for(Temp_tempList defs = FG_def(flownodes->head); defs; defs = defs->tail) {
			getOrCreateNode(lg.graph, defs->head, temp_node_table, lg.priorities);
		}
	}

	for(G_nodeList flownodes = G_nodes(flow); flownodes; flownodes = flownodes->tail) {
		Temp_tempList liveouts = lookupLiveMap(out_set_table, flownodes->head);
		if(FG_isMove(flownodes->head)) {
			liveouts = Temp_difference(liveouts, FG_use(flownodes->head));
			for(Temp_tempList defs = FG_def(flownodes->head); defs; defs = defs->tail) {
				for(Temp_tempList uses = FG_use(flownodes->head); uses; uses = uses->tail) {
					if(uses->head != F_FP() && defs->head != F_FP()) {
						lg.moves = Live_union(lg.moves, Live_MoveList(getOrCreateNode(lg.graph, uses->head, temp_node_table, lg.priorities),
																			getOrCreateNode(lg.graph, defs->head, temp_node_table, lg.priorities),
																			NULL));
					}
        }
      }
		}

		for(Temp_tempList defs = FG_def(flownodes->head); defs; defs = defs->tail) {
			for(Temp_tempList outs = liveouts; outs; outs = outs->tail) {
				addEdge(lg.graph, defs->head, outs->head, temp_node_table, lg.priorities);
			}
		}
	}

	return lg;
}
