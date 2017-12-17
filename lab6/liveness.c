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

static Temp_tempList unionSet(Temp_tempList set1, Temp_tempList set2) {
	Temp_tempList res = NULL;
	for(Temp_tempList temps1 = set1; temps1; temps1 = temps1->tail) {
		res = Temp_TempList(temps1->head, res);
	}

	for(Temp_tempList temps2 = set2; temps2; temps2 = temps2->tail) {
		bool found = false;
		for(Temp_tempList temps1 = set1; temps1; temps1 = temps1->tail) {
			if(temps1->head == temps2->head) {
				found = true;
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
		bool found = false;
		for(Temp_tempList temps2 = set2; temps2; temps2 = temps2->tail) {
			if(temps1->head == temps2->head) {
				found = true;
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
		bool found = false;
		for(Temp_tempList temps2 = set2; temps2; temps2 = temps2->tail) {
			if(temps1->head == temps2->head) {
				found = true;
				break;
			}
		}
		if(!found) {
			return false;
		}
	}
	return true;
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

struct Live_graph Live_liveness(G_graph flow) {
	//your code here.
	struct Live_graph lg;
	lg.graph = G_Graph();
	lg.moves = NULL;
	G_nodeList flownodes;

	// calculate the in/out set and begin liveness analysis
	G_table in_set_table = G_empty();
	G_table out_set_table = G_empty();
	bool has_change = true;

	while(has_change) {
		has_change = false;
		for(flownodes = G_nodes(flow); flownodes; flownodes = flownodes->tail) {
			Temp_tempList old_in_set = lookupLiveMap(in_set_table, flownodes->head);
			Temp_tempList old_out_set = lookupLiveMap(out_set_table, flownodes->head);
			Temp_tempList use_set = FG_use(flownodes->head);
			Temp_tempList def_set = FG_def(flownodes->head);

			Temp_tempList new_in_set = unionSet(use_set, differenceSet(old_out_set, def_set));
			Temp_tempList new_out_set = NULL;

			for(G_nodeList nodes = G_succ(flownodes->head); nodes; nodes = nodes->tail) {
				new_out_set = unionSet(new_out_set, lookupLiveMap(in_set_table, nodes->head));
			}

			if(!equalSet(old_in_set, new_in_set) || !equal(old_out_set, new_out_set)) {
				has_change = true;
			}
		}
	}

	// construct interference graph
	for(flownodes = G_nodes(flow); flownodes; flownodes = flownodes->tail) {
		if(FG_isMove(flownodes->head)) {
			lg.move = Live_MoveList()
		}
	}

	return lg;
}
