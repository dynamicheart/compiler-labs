#include <stdio.h>
#include <stdlib.h>
#include "util.h"
#include "symbol.h"
#include "absyn.h"
#include "temp.h"
#include "errormsg.h"
#include "tree.h"
#include "assem.h"
#include "frame.h"
#include "codegen.h"
#include "table.h"

//Lab 6: put your code here

#define MAXLINE 40

static AS_instrList iList = NULL, last = NULL;
static void emit(AS_instr inst);
static void munchStm(T_stm s);
static Temp_temp munchExp(T_exp e);
static Temp_tempList munchArgs();
static Temp_tempList L(Temp_temp h, Temp_tempList t);

static void emit(AS_instr inst) {
  if(last != NULL)
    last = last->tail = AS_InstrList(instr, NULL);
  else last = iList = AS_InstrList(inst, NULL);
}

static void munchStm(T_stm s) {
  switch(s->kind) {
    case T_MOVE: {
      T_exp dst = s->u.MOVE.dst, src = s->u.MOVE.src;
      if(dst->kind == T_MEM) {
        if(dst->u.MEM->kind == T_BINOP
          && dst->u.MEM->u.BINOP.op == T_plus
          && dst->u.MEM->u.BINOP.right->kind == T_CONST) {
            /*MOVE(MEM(BINOP(PLUS, e1, CONST(n))), e2) */
            T_exp e1 = dst->u.MEM->u.BINOP.left, e2 = src;
            int n = dst->u.MEM->u.BINOP.right->u.CONST;
            char *a = checked_malloc(MAXLINE * sizeof(char));
            sprintf(a, "movl %d(`s0), `s1\n", n);
            emit(AS_Oper(a, NULL, L(munchExp(e2), L(mumchExp(e1), NULL)), NULL));
        }
        else if(dst->u.MEM->kind == T_BINOP
          && dst->u.MEM->u.BINOP.op == T_plus
          && dst->u.MEM->u.BINOP.left->kind == T_CONST) {
            /*MOVE(MEM(BINOP(PLUS, CONST(n), e1)), e2) */
            T_exp e1 = dst->u.MEM->u.BINOP.left, e2 = src;
            int n = dst->u.MEM->u.BINOP.left->u.CONST;
            char *a = checked_malloc(MAXLINE * sizeof(char));
            sprintf(a, "movl %d(`s0), `s1\n", n);
            emit(AS_Oper(a, NULL, L(munchExp(e2), L(mumchExp(e1), NULL)), NULL));
        }
        else if(src->kind == T_MEM) {
          /*MOVE(MEM(e1), MEM(e2)) */
          T_exp e1 = dst->u.MEM, e2 = src->u.MEM;
          emit(AS_Oper("movl (`s0`), `s1\n`"), NULL, L(munchExp(e1), L(munchExp(e2), NULL)), NULL);
        }
        else {

        }
      }
      else if (dst->kind == T_TEMP) {

      }
      else assert(0);
      break;
    }
    case T_JUMP: {
      T_exp e = s->u.JUMP.exp;
      if(e->kind == T_NAME) {
        char *a = checked_malloc(MAXLINE * sizeof(char));
        sprintf(a, "jmp %s\n", Temp_labelstring(e->u.NAME));
        emit(AS_Oper(a, NULL, NULL, AS_targets(s->u.JUMP.jumps)));
      }else {
        emit(AS_Oper("jmp *`s0\n", NULL, L(munchExp(e), NULL), AS_targets(s->u.JUMP.jumps)));
      }
      break;
    }
    case T_CJUMP: {

    }
    case T_EXP:
      munchExp(s->u.EXP);
      break;
    case T_LABEL: {
      char *a = checked_malloc(MAXLINE * sizeof(char));
      sprintf(a, "%s:\n", Temp_labelstring(s->u.LABEL));
      emit(AS_Oper(a, NULL, NULL, NULL));
      break;
    }
    case T_SEQ:
      munchStm(s->u.SEQ.left);
      munchStm(s->u.SEQ.right);
      break;
    default:
      assert(0);
  }
}

static Temp_temp mumchExp(T_exp e) {
  switch(e->kind) {
    case T_BINOP: {
      Temp_temp ltemp = munchExp(e->u.BINOP.left), rtemp = munchExp(e->u.BINOP.right);
      switch(e->u.BINOP.op) {
        case T_plus:
          emit(AS_Oper("addl `s1, `d0"), L(ltemp, NULL), L(ltemp, L(rtemp, NULL)), NULL);
          break;
        case T_minus:
          emit(AS_Oper("subl `s1, `d0"), L(ltemp, NULL), L(ltemp, L(rtemp, NULL)), NULL);
          break;
        case T_mul:
          emit(AS_Oper("imull `s1, `d0"), L(ltemp, NULL), L(ltemp, L(rtemp, NULL)), NULL);
          break;
        case T_div:
          emit(AS_Oper("addl `s1, `d0"), L(ltemp, NULL), L(ltemp, L(rtemp, NULL)), NULL);
          break;
        default:
          assert(0);
      }
    }
    case T_MEM: {

    }
    case T_TEMP:
      return e->u.TEMP;
    case T_NAME: {
      Temp_temp temp = Temp_newtemp();
      char *a = checked_malloc(MAXLINE * sizeof(char));
      sprintf(a, "movl $%s, `d0\n", Temp_labelstring(e->u.NAME));
      emit(AS_Oper(a, L(temp, NULL), NULL, NULL));
      return temp;
    }
    case T_CONST: {
      Temp_temp temp = Temp_newtemp();
      char *a = checked_malloc(MAXLINE * sizeof(char));
      sprintf(a, "movl $%d, `d0\n", e->u.CONST);
      emit(AS_Oper(a, L(temp, NULL), NULL, NULL));
      return temp;
    }
    case T_CALL: {
      
    }
    case T_ESEQ:
    default:
      assert(0);
  }
}

static Temp_templist L(Temp_temp h, Temp_tempList t) {
  return Temp_TempList(h, t);
}

AS_instrList F_codegen(F_frame f, T_stmList stmList) {
  AS_instrList list;
  T_stmList sl;

  for(sl = stmList; sl; sl = sl->tail) {
    munchStm(sl->head);
  }
  list = iList;
  iList = last = NULL;
  return list;
}
