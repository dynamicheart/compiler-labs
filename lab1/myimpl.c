#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include "prog1.h"
#define MAX(a,b)            (((a) > (b)) ? (a) : (b))

typedef struct table *Table_;
struct table {string id; int value; Table_ tail;};
static Table_ Table(string id, int value, Table_ tail) {
  Table_ t = malloc(sizeof(*t));
  t->id=id; t->value=value; t->tail=tail;
  return t;
}

struct IntAndTable {int i; Table_ t;};
static struct IntAndTable IntAndTable(int value, Table_ table){
  struct IntAndTable intAndTable;
  intAndTable.i = value; intAndTable.t = table;
  return intAndTable;
}

static int maxargsExp(A_exp);
static int maxargsExpList(A_expList);
static int numsExpList(A_expList);
static Table_ interpStm(A_stm, Table_);
static Table_ interpExpList(A_expList, Table_);
static struct IntAndTable interpExp(A_exp, Table_);
static int lookup(Table_, string);
static Table_ update(Table_, string, int);

int maxargs(A_stm stm)
{
  switch(stm->kind){
    case A_compoundStm:
      return MAX(maxargs(stm->u.compound.stm1), maxargs(stm->u.compound.stm2));
    case A_assignStm:
      return maxargsExp(stm->u.assign.exp);
    case A_printStm:
      return MAX(numsExpList(stm->u.print.exps), maxargsExpList(stm->u.print.exps));
    default:
      printf("Unsupported statement type.\n");
      assert(0);
  }
}

void interp(A_stm stm)
{
  Table_ t = interpStm(stm, NULL);
}

int maxargsExp(A_exp exp)
{
  switch(exp->kind){
    case A_idExp:
    case A_numExp:
      break;
    case A_opExp:
      return MAX(maxargsExp(exp->u.op.left), maxargsExp(exp->u.op.right));
    case A_eseqExp:
      return MAX(maxargs(exp->u.eseq.stm),maxargsExp(exp->u.eseq.exp));
    default:
      printf("Unsupported expression type.\n");
      assert(0);
  }
}

int maxargsExpList(A_expList exp_list)
{
  switch(exp_list->kind){
    case A_pairExpList:
      return MAX(maxargsExp(exp_list->u.pair.head), maxargsExpList(exp_list->u.pair.tail));
    case A_lastExpList:
      return maxargsExp(exp_list->u.last);
    default:
      printf("Unsupported expression list type.\n");
      assert(0);
  }
}

int numsExpList(A_expList exps)
{
  if(exps->kind == A_lastExpList){
    return 1;
  }
  return 1 + numsExpList(exps->u.pair.tail);
}

Table_ interpStm(A_stm s, Table_ t){
  switch(s->kind){
    case A_compoundStm:
      {
        Table_ resStm1 = interpStm(s->u.compound.stm1, t);
        return interpStm(s->u.compound.stm2, resStm1);
      }
    case A_assignStm:
      {
        struct IntAndTable resExp = interpExp(s->u.assign.exp, t);
        return Table(s->u.assign.id, resExp.i, resExp.t);
      }
    case A_printStm:
      return interpExpList(s->u.print.exps, t);
    default:
      printf("Unsupported statement type.\n");
      assert(0);
  }
}

Table_ interpExpList(A_expList exps, Table_ t)
{
  switch(exps->kind){
    case A_pairExpList:
      {
        struct IntAndTable resExp = interpExp(exps->u.pair.head, t);
        printf("%d ", resExp.i);
        return interpExpList(exps->u.pair.tail, resExp.t);
      }
    case A_lastExpList:
      {
        struct IntAndTable resExp = interpExp(exps->u.last, t);
        printf("%d \n", resExp.i);
        return resExp.t;
      }
    default:
      printf("Unsupported expression list type.\n");
      assert(0);
  }
}

struct IntAndTable interpExp(A_exp e, Table_ t){
  switch(e->kind){
    case A_idExp:
      return IntAndTable(lookup(t, e->u.id), t); 
    case A_numExp:
      return IntAndTable(e->u.num, t);
    case A_opExp:
      {
        struct IntAndTable resLeftExp = interpExp(e->u.op.left, t);
        struct IntAndTable resRightExp = interpExp(e->u.op.right, resLeftExp.t);
        switch(e->u.op.oper){
          case A_plus:
            return IntAndTable(resLeftExp.i + resRightExp.i, resRightExp.t);
          case A_minus:
            return IntAndTable(resLeftExp.i - resRightExp.i, resRightExp.t);
          case A_times:
            return IntAndTable(resLeftExp.i * resRightExp.i, resRightExp.t);
          case A_div:
            return IntAndTable(resLeftExp.i / resRightExp.i, resRightExp.t);
          default:
            printf("Unsuported operation.\n");
            assert(0);
        }
      }
    case A_eseqExp:
      {
        Table_ resStm = interpStm(e->u.eseq.stm, t);
        struct IntAndTable resExp = interpExp(e->u.eseq.exp, resStm);
        return IntAndTable(resExp.i, resExp.t);
      }
    default:
      printf("Unsupported expression type.\n");
      assert(0);
  }
}

int lookup(Table_ t, string key)
{
  if(!t){
    printf("%s is used without declaration.\n", key);
    assert(0);
  }

  if(t->id == key){
    return t->value;
  }else{
    return lookup(t->tail, key);
  }
}

Table_ update(Table_ t, string key, int value)
{
  return Table(key, value, t);
}

