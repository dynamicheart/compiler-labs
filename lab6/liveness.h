#ifndef LIVENESS_H
#define LIVENESS_H

typedef struct Live_moveList_ *Live_moveList;
struct Live_moveList_ {
	G_node src, dst;
	Live_moveList tail;
};

Live_moveList Live_MoveList(G_node src, G_node dst, Live_moveList tail);

Live_moveList Live_union(Live_moveList moves_a, Live_moveList moves_b);
Live_moveList Live_difference(Live_moveList moves_a, Live_moveList moves_b);
bool Live_inMoveList(Live_moveList moves, G_node src, G_node dst);

struct Live_graph {
	G_graph graph;
	Live_moveList moves;
	G_table priorities;
};
Temp_temp Live_gtemp(G_node n);

struct Live_graph Live_liveness(G_graph flow);

#endif
