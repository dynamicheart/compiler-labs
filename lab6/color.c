#include <stdio.h>
#include <string.h>

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
#include "table.h"

#define K 6
#define BUF_SIZE 40

static char *color_names[7] = {"uncolored", "%eax", "%ebx", "%ecx", "%edx", "%esi", "%edi"};

// Node work-lists, sets and stack
static G_nodeList precolored;
static G_nodeList simplifyWorklist;
static G_nodeList freezeWorklist;
static G_nodeList spillWorklist;
static G_nodeList spilledNodes;
static G_nodeList coalescedNodes;
static G_nodeList coloredNodes;
static G_nodeList selectStack;

// Move sets
static Live_moveList coalescedMoves;
static Live_moveList constrainedMoves;
static Live_moveList frozenMoves;
static Live_moveList worklistMoves;
static Live_moveList activeMoves;

// Other data structure
static G_graph graph;
static G_table degree;
static G_table color;
static G_table alias;
static G_table priorities;
static G_table nodemoves;

/* ==================IMPLEMENTATION BEGIN ===================== */
static bool isPrecolored(G_node n);
static void build(struct Live_graph lg, Temp_tempList regs);
static void addEdge(G_node u, G_node v);
static void makeWorklist();
static G_nodeList adjacent(G_node n);
static Live_moveList nodeMoves(G_node n);
static bool moveRelated(G_node n);
static void simplify();
static void decrementDegree(G_node n);
static void enableMoves(G_nodeList nodes);
static void coalesce();
static void addWorkList(G_node n);
static bool OK(G_node v, G_node r);
static bool conservative(G_nodeList nodes);
static G_node getAlias(G_node n);
static void combine(G_node u, G_node v);
static void freeze();
static void freezeMoves(G_node u);
static void selectSpill();
static void assignColors();
static Temp_tempList getSpills();
static Temp_map getColorMap();

static bool isPrecolored(G_node n)
{
	for(G_nodeList nodes = precolored; nodes; nodes = nodes->tail) {
		if(n == nodes->head) {
			return TRUE;
		}
	}
	return FALSE;
}

static void build(struct Live_graph lg, Temp_tempList regs)
{
	precolored = NULL;
	simplifyWorklist = NULL;
	freezeWorklist = NULL;
	spillWorklist = NULL;
	spilledNodes = NULL;
	coalescedNodes = NULL;
	selectStack = NULL;

	coalescedMoves = NULL;
	constrainedMoves = NULL;
	frozenMoves = NULL;
	worklistMoves = lg.moves;
	activeMoves = NULL;

	degree = G_empty();
	color = G_empty();
	alias = G_empty();
	graph = lg.graph;
	priorities = lg.priorities;
	nodemoves = G_empty();
	for(G_nodeList nodes = G_nodes(graph); nodes; nodes = nodes->tail) {
		int *d = checked_malloc(sizeof(int));
		*d = G_outDegree(nodes->head);
		G_enter(degree, nodes->head, d);

		//color machine regs
		int *c = checked_malloc(sizeof(sizeof(int)));
		Temp_temp temp = Live_gtemp(nodes->head);
		if(temp == F_EAX()) {
			*c = 1;
			precolored = G_NodeList(nodes->head, precolored);
		}else if(temp == F_EBX()) {
			*c = 2;
			precolored = G_NodeList(nodes->head, precolored);
		}else if(temp == F_ECX()) {
			*c = 3;
			precolored = G_NodeList(nodes->head, precolored);
		}else if(temp == F_EDX()) {
			*c = 4;
			precolored = G_NodeList(nodes->head, precolored);
		}else if(temp == F_ESI()) {
			*c = 5;
			precolored = G_NodeList(nodes->head, precolored);
		}else if(temp == F_EDI()) {
			*c = 6;
			precolored = G_NodeList(nodes->head, precolored);
		}else {
			*c = 0;
		}
		G_enter(color, nodes->head, c);

		G_enter(nodemoves, nodes->head, G_NodeList(nodes->head, NULL));
	}
}


static void addEdge(G_node u, G_node v)
{
	if(!G_isAdj(u, v) && u != v) {
		G_addAdj(u, v);
		if(!isPrecolored(u)) {
			G_addEdge(u, v);
			int *d = G_look(degree, u);
			*d = *d + 1;
		}
		if (!isPrecolored(v)) {
			G_addEdge(v, u);
			int *d = G_look(degree, v);
			*d = *d + 1;
		}
	}
}

static void makeWorklist()
{
	G_nodeList nodes = G_nodes(graph);
	for(; nodes; nodes = nodes->tail) {
		int *d = G_look(degree, nodes->head);
		int *c = G_look(color, nodes->head);
		if(!isPrecolored(nodes->head)) {
			if(*d >= K) spillWorklist = G_NodeList(nodes->head, spillWorklist);
			else if(moveRelated(nodes->head)) freezeWorklist = G_NodeList(nodes->head, freezeWorklist);
			else simplifyWorklist = G_NodeList(nodes->head, simplifyWorklist);
		}
	}
}

static G_nodeList adjacent(G_node n)
{
	return G_difference(G_succ(n), G_union(selectStack, coloredNodes));
}

static Live_moveList nodeMoves(G_node n)
{
	Live_moveList moves = Live_union(activeMoves, worklistMoves);
	G_nodeList nodemoves_n = G_look(nodemoves, n);
	Live_moveList res = NULL;
	for(; moves; moves = moves->tail) {
		for(G_nodeList nodes = nodemoves_n; nodes; nodes = nodes->tail) {
			if(moves->src == nodes->head || moves->dst == nodes->head) {
				res = Live_MoveList(moves->src, moves->dst, res);
			}
		}
	}

	return res;
}

static bool moveRelated(G_node n)
{
	return nodeMoves(n) != NULL;
}

static void simplify()
{
	G_node n = simplifyWorklist->head;
	simplifyWorklist = simplifyWorklist->tail;
	selectStack = G_NodeList(n, selectStack);
	for(G_nodeList nodes = adjacent(n); nodes; nodes = nodes->tail) {
		decrementDegree(nodes->head);
	}
}

static void decrementDegree(G_node m)
{
	int *d = G_look(degree, m);
	int old_d = *d;
	*d = *d - 1;
	if(old_d == K) {
		enableMoves(G_NodeList(m, adjacent(m)));
		spillWorklist = G_difference(spillWorklist, G_NodeList(m, NULL));
		if(moveRelated(m)) freezeWorklist = G_NodeList(m, freezeWorklist);
		else simplifyWorklist = G_NodeList(m, simplifyWorklist);
	}
}

static void enableMoves(G_nodeList nodes)
{
	for(; nodes; nodes = nodes->tail) {
		for(Live_moveList moves = nodeMoves(nodes->head); moves; moves = moves->tail) {
			if(Live_inMoveList(activeMoves, moves->src, moves->dst)) {
				activeMoves = Live_difference(activeMoves, Live_MoveList(moves->src, moves->dst, NULL));
				worklistMoves = Live_MoveList(moves->src, moves->dst, worklistMoves);
			}
		}
	}
}

static void coalesce()
{
	G_node u, v;
	G_node x = getAlias(worklistMoves->src), y = getAlias(worklistMoves->dst);
	if(isPrecolored(y)) {
		u = y;
		v = x;
	}else {
		u = x;
		v = y;
	}
	worklistMoves = worklistMoves->tail;
	bool adj = G_isAdj(u, y);
	if(u == v) {
		coalescedMoves = Live_MoveList(u, v, coalescedMoves);
		addWorkList(u);
	}else if(isPrecolored(v) || adj) {
		constrainedMoves = Live_MoveList(u, v, constrainedMoves);
		addWorkList(u);
		addWorkList(v);
	}else if((isPrecolored(u) && OK(v, u)) || (!isPrecolored(u) && conservative(G_union(adjacent(u), adjacent(v))))) {
		coalescedMoves = Live_MoveList(u, v, coalescedMoves);
		combine(u, v);
		addWorkList(u);
	}else {
		activeMoves = Live_MoveList(u, v, activeMoves);
	}
}

static void addWorkList(G_node u)
{
	int *d = G_look(degree, u);
	if(!isPrecolored(u) && !(moveRelated(u) && *d < K)) {
		freezeWorklist = G_difference(freezeWorklist, G_NodeList(u, NULL));
		simplifyWorklist = G_NodeList(u, simplifyWorklist);
	}
}

static bool OK(G_node v, G_node r)
{
	//TODO nodes->head is r
	for(G_nodeList nodes = adjacent(v); nodes; nodes = nodes->tail) {
		int *d = G_look(degree, nodes->head);
		bool adj = G_isAdj(nodes->head, r);
		if(!(*d <= K || isPrecolored(nodes->head) || adj)) {
			return FALSE;
		}
	}
	return TRUE;
}

static bool conservative(G_nodeList nodes)
{
	int k = 0;
	for(; nodes; nodes = nodes->tail) {
		int *d = G_look(degree, nodes->head);
		if(*d >= K) {
			k++;
		}
	}
	return k < K;
}

static G_node getAlias(G_node n)
{
	for(G_nodeList nodes = coalescedNodes; nodes; nodes = nodes->tail) {
		if(n == nodes->head) {
			G_node a = G_look(alias, n);
			return getAlias(a);
		}
	}
	return n;
}

static void combine(G_node u, G_node v)
{
	if(G_inNodeList(v, freezeWorklist)) freezeWorklist = G_difference(freezeWorklist, G_NodeList(v, NULL));
	else spillWorklist = G_difference(spillWorklist, G_NodeList(v, NULL));

	coalescedNodes = G_NodeList(v, coalescedNodes);
	G_enter(alias, v, u);

	G_nodeList nodemoves_u = G_look(nodemoves, u);
	nodemoves_u = G_NodeList(v, nodemoves_u );
	G_enter(nodemoves, u, nodemoves_u);
	for(G_nodeList nodes = adjacent(v); nodes; nodes = nodes->tail) {
		addEdge(nodes->head, u);
		decrementDegree(nodes->head);
	}

	int *d = G_look(degree, u);
	if(*d >= K && G_inNodeList(u, freezeWorklist)) {
		freezeWorklist = G_difference(freezeWorklist, G_NodeList(u, NULL));
		spillWorklist = G_union(spillWorklist, G_NodeList(u, NULL));
	}
}

static void freeze()
{
	G_node u = freezeWorklist->head;
	freezeWorklist = freezeWorklist->tail;
	simplifyWorklist = G_NodeList(u, simplifyWorklist);
	freezeMoves(u);
}

static void freezeMoves(G_node u)
{
	for(Live_moveList moves = nodeMoves(u); moves; moves = moves->tail) {
		G_node v;
		if(getAlias(moves->dst) == getAlias(u)){
			v = getAlias(moves->src);
		}else {
			v = getAlias(moves->dst);
		}
		activeMoves = Live_difference(activeMoves, Live_MoveList(moves->src, moves->dst, NULL));
		frozenMoves = Live_MoveList(moves->src, moves->dst, frozenMoves);
		int *d = G_look(degree, v);
		if(!nodeMoves(v) && *d < K) {
			freezeWorklist = G_difference(freezeWorklist, G_NodeList(v, NULL));
			simplifyWorklist = G_NodeList(v, simplifyWorklist);
		}
	}
}

static void selectSpill()
{
	G_node m = spillWorklist->head;
	//TODO
	spillWorklist = spillWorklist->tail;
	simplifyWorklist = G_NodeList(m, simplifyWorklist);
	freezeMoves(m);
}

static void assignColors()
{
	while(selectStack) {
		G_node n = selectStack->head;
		selectStack = selectStack->tail;
		bool okColors[K];
		memset(okColors, TRUE, K);
		for(G_nodeList nodes = G_succ(n); nodes; nodes = nodes->tail) {
			G_node a = getAlias(nodes->head);
			if(G_inNodeList(a, G_union(coloredNodes, precolored))){
				int *c = G_look(color, a);
				okColors[*c - 1] = FALSE;
			}
		}

		bool empty = TRUE;
		int actual_c;
		for(int i = 0; i < K; i++) {
			if(okColors[i] == TRUE){
				empty = FALSE;
				actual_c = i + 1;
				break;
			}
		}
		if(empty) {
			spilledNodes = G_NodeList(n, spilledNodes);
		}else {
			coloredNodes = G_NodeList(n, coloredNodes);
			int *c = G_look(color, n);
			*c = actual_c;
		}

	}
	for(G_nodeList nodes = coalescedNodes; nodes; nodes = nodes->tail) {
		int *actual_c = G_look(color, getAlias(nodes->head));
		int *c = G_look(color, nodes->head);
		*c = *actual_c;
	}
}

static Temp_tempList getSpills() {
	Temp_tempList res = NULL;
	for(G_nodeList nodes = spilledNodes; nodes; nodes = nodes->tail){
		res = Temp_TempList(Live_gtemp(nodes->head), res);
	}
	return res;
}

static Temp_map getColorMap() {
	Temp_map res = Temp_empty();
	for(G_nodeList nodes = G_nodes(graph); nodes; nodes = nodes->tail) {
		int *c = G_look(color, nodes->head);
		Temp_enter(res, Live_gtemp(nodes->head), color_names[*c]);
	}
	Temp_enter(res, F_FP(), "%ebp");
	return res;
}

struct COL_result COL_color(struct Live_graph lg, Temp_map initial, Temp_tempList regs) {
	//your code here.
	build(lg, regs);
	makeWorklist();
	do {
		if(simplifyWorklist) simplify();
		else if(worklistMoves) coalesce();
		else if(freezeWorklist) freeze();
		else if(spillWorklist) selectSpill();
	} while(simplifyWorklist || worklistMoves || freezeWorklist || spillWorklist);
	assignColors();

	struct COL_result ret;
	ret.spills = getSpills();
	ret.coloring = getColorMap();

	return ret;
}
