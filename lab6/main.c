/*
 * main.c
 */

#include <stdio.h>
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "types.h"
#include "absyn.h"
#include "errormsg.h"
#include "temp.h" /* needed by translate.h */
#include "tree.h" /* needed by frame.h */
#include "assem.h"
#include "frame.h" /* needed by translate.h and printfrags prototype */
#include "translate.h"
#include "env.h"
#include "semant.h" /* function prototype for transProg */
#include "canon.h"
#include "prabsyn.h"
#include "printtree.h"
#include "escape.h"
#include "parse.h"
#include "codegen.h"
#include "graph.h"
#include "flowgraph.h"
#include "liveness.h"
#include "regalloc.h"

extern bool anyErrors;

static showRegs(Temp_temp temp)
{
  fprintf(stdout, "%s ", Temp_look(Temp_layerMap(F_tempMap(), Temp_name()), temp));
}

/*Lab6: complete the function doProc
 * 1. initialize the F_tempMap
 * 2. initialize the register lists (for register allocation)
 * 3. do register allocation
 * 4. output (print) the assembly code of each function

 * Uncommenting the following printf can help you debugging.*/

/* print the assembly language instructions to filename.s */
static void doProc(FILE *out, F_frame frame, T_stm body)
{
 AS_proc proc;
 T_stmList stmList;
 AS_instrList iList;
 struct C_block blo;

 // printf("doProc for function %s:\n", S_name(F_name(frame)));
 // printStmList(stdout, T_StmList(body, NULL));
 // printf("-------====IR tree=====-----\n");

 stmList = C_linearize(body);
 // printStmList(stdout, stmList);
 // printf("-------====Linearlized=====-----\n");

 blo = C_basicBlocks(stmList);
 // C_stmListList stmLists = blo.stmLists;
 // for (; stmLists; stmLists = stmLists->tail) {
 // printStmList(stdout, stmLists->head);
 // printf("------====Basic block=====-------\n");
 // }

 stmList = C_traceSchedule(blo);
 printStmList(stdout, stmList);
 printf("-------====trace=====-----\n");
 iList  = F_codegen(frame, stmList); /* 9 */

 AS_printInstrList(stdout, iList, Temp_layerMap(F_tempMap(), Temp_name()));
 printf("----======before RA=======-----\n");

 G_graph fg = FG_AssemFlowGraph(iList, frame);  /* 10.1 */
 G_show(stdout, G_nodes(fg), NULL);

 printf("----======Flowgraph=======-----\n");
 struct Live_graph lg = Live_liveness(fg);
 G_show(stdout, G_nodes(lg.graph), showRegs);
 printf("----======interference graph=======-----\n");
 
 struct RA_result ra_result = RA_regAlloc(frame, iList);

 // AS_printInstrList(stdout, ra_result.il, Temp_layerMap(ra_result.coloring, Temp_name()));
 // printf("----===========after RA============-----\n");

 string procName = S_name(F_name(frame));
 fprintf(out, ".text\n");
 fprintf(out, ".globl %s\n", procName);
 fprintf(out, ".type %s, @function\n", procName);
 fprintf(out, "%s:\n", procName);

 //prologue
 fprintf(out, "pushl %%ebp\n");
 fprintf(out, "movl %%esp, %%ebp\n");
 fprintf(out, "subl $%d, %%esp\n", F_frameSize(frame));

 AS_printInstrList (out, ra_result.il, ra_result.coloring);
}

void doStr(FILE *out, Temp_label label, string str) {
	fprintf(out, ".section .rodata\n");
	fprintf(out, "%s:\n", S_name(label));
  fprintf(out, ".int %ld\n", strlen(str));
	fprintf(out, ".string \"");
	for (; *str; str++) {
    if(*str == '\n') fprintf(out, "\\n");
    else if(*str == '\t') fprintf(out, "\\t");
    else fprintf(out, "%c", *str);
	}
	fprintf(out, "\"\n");

}

int main(int argc, string *argv)
{
 A_exp absyn_root;
 S_table base_env, base_tenv;
 F_fragList frags;
 char outfile[100];
 FILE *out = stdout;

 if (argc==2) {
   absyn_root = parse(argv[1]);
   if (!absyn_root)
     return 1;

#if 0
   pr_exp(out, absyn_root, 0); /* print absyn data structure */
   fprintf(out, "\n");
#endif

   //Lab 6: escape analysis
   //If you have implemented escape analysis, uncomment this
   Esc_findEscape(absyn_root); /* set varDec's escape field */

   frags = SEM_transProg(absyn_root);
   if (anyErrors) return 1; /* don't continue */

   /* convert the filename */
   sprintf(outfile, "%s.s", argv[1]);
   out = fopen(outfile, "w");
   /* Chapter 8, 9, 10, 11 & 12 */
   for (;frags;frags=frags->tail)
     if (frags->head->kind == F_procFrag) {
       doProc(out, frags->head->u.proc.frame, frags->head->u.proc.body);
     }
     else if (frags->head->kind == F_stringFrag) {
       doStr(out, frags->head->u.stringg.label, frags->head->u.stringg.str);
     }

   fclose(out);
   return 0;
 }
 EM_error(0,"usage: tiger file.tig");
 return 1;
}
