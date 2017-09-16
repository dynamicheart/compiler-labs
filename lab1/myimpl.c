#include <stdio.h>
#include <stdlib.h>
#include "prog1.h"
#define MAX(a,b)            (((a) > (b)) ? (a) : (b))
#define MIN(a,b)            (((a) < (b)) ? (a) : (b))
typedef struct table *Table_;
struct table {string id; int value; Table_ tail;};
struct IntAndTable {int i; Table_ t;};

static int maxargs_exp(A_exp exp);
static int maxargs_exp_list(A_expList exp_list);
static int calculate_print_stm_args(A_stm stm);

static Table_ Table(string id, int value, struct table *tail);
static Table_ interpStm(A_stm s, Table_ t);
static struct IntAndTable interpExp(A_exp e, Table_ t);

static int lookup(Table_ t, string key);
static Table_ update(Table_ t, string key, int value);

static void free_table(Table_ t);

int maxargs(A_stm stm){
    switch(stm->kind){
        case A_compoundStm:
            return MAX(maxargs(stm->u.compound.stm1), maxargs(stm->u.compound.stm2));
        case A_assignStm:
            return maxargs_exp(stm->u.assign.exp);
        case A_printStm:
            return MAX(calculate_print_stm_args(stm), maxargs_exp_list(stm->u.print.exps));
        default:
            printf("Unsupported statement type.\n");
            exit(1);
    }
	return 0;
}

void interp(A_stm stm){
    Table_ t = interpStm(stm, NULL);
    free_table(t);
}

int maxargs_exp(A_exp exp){
    switch(exp->kind){
        case A_idExp:
        case A_numExp:
            break;
        case A_opExp:
            return MAX(maxargs_exp(exp->u.op.left), maxargs_exp(exp->u.op.right));
        case A_eseqExp:
            return MAX(maxargs(exp->u.eseq.stm),maxargs_exp(exp->u.eseq.exp));
        default:
            printf("Unsupported expression type.\n");
            exit(1);
    }
    return 0;
}

int maxargs_exp_list(A_expList exp_list)
{
    switch(exp_list->kind){
        case A_pairExpList:
            return MAX(maxargs_exp(exp_list->u.pair.head), maxargs_exp_list(exp_list->u.pair.tail));
        case A_lastExpList:
            return maxargs_exp(exp_list->u.last);
        default:
            printf("Unsupported expression list type.\n");
            exit(1);
    }
    return 0;
}

int calculate_print_stm_args(A_stm stm){
    int args = 1;
    A_expList currrent_exp_list = stm->u.print.exps;
    while(currrent_exp_list->kind == A_pairExpList){
        args++;
        currrent_exp_list = currrent_exp_list->u.pair.tail;
    }
    return args;
}

Table_ Table(string id, int value, struct table *tail) {
    Table_ t = malloc(sizeof(*t));
    t->id=id; t->value=value; t->tail=tail;
    return t;
}

Table_ interpStm(A_stm s, Table_ t){
    if(s->kind == A_compoundStm){
        Table_ table_after_stm1 = interpStm(s->u.compound.stm1, t);
        return interpStm(s->u.compound.stm2, table_after_stm1);
    }else if(s->kind == A_assignStm){
        struct IntAndTable result_after_exp = interpExp(s->u.assign.exp, t);
        return Table(s->u.assign.id, result_after_exp.i, result_after_exp.t);
    }else if(s->kind == A_printStm){
        A_expList currrent_exp_list = s->u.print.exps;
        Table_ current_table = t;
        while(currrent_exp_list->kind == A_pairExpList){
            struct IntAndTable result_after_exp = interpExp(currrent_exp_list->u.pair.head, current_table);
            current_table =  result_after_exp.t;
            printf("%d ", result_after_exp.i);
            currrent_exp_list = currrent_exp_list->u.pair.tail;
        }
        struct IntAndTable result_after_last_exp_list = interpExp(currrent_exp_list->u.last, current_table);
        printf("%d \n", result_after_last_exp_list.i);
        return result_after_last_exp_list.t;
    }else{
        printf("Unsupported statement type.\n");
        exit(1);
    }
}

struct IntAndTable interpExp(A_exp e, Table_ t){
    struct IntAndTable result;
    if(e->kind == A_idExp){
        result.i = lookup(t, e->u.id); result.t = t;
    }else if(e->kind == A_numExp){
        result.i = e->u.num; result.t = t;
    }else if(e->kind == A_opExp){
        struct IntAndTable result_after_left_exp = interpExp(e->u.op.left, t);
        struct IntAndTable result_after_right_exp = interpExp(e->u.op.right, result_after_left_exp.t);
        switch(e->u.op.oper){
            case A_plus:
                result.i = result_after_left_exp.i + result_after_right_exp.i;
                break;
            case A_minus:
                result.i = result_after_left_exp.i - result_after_right_exp.i;
                break;
            case A_times:
                result.i = result_after_left_exp.i * result_after_right_exp.i;
                break;
            case A_div:
                result.i = result_after_left_exp.i / result_after_right_exp.i;
                break;
            default:
                printf("Unsuported operation.\n");
                exit(1);
        }
        result.t = result_after_right_exp.t;
    }else if(e->kind == A_eseqExp){
        Table_ table_after_stm = interpStm(e->u.eseq.stm, t);
        struct IntAndTable result_after_exp = interpExp(e->u.eseq.exp, table_after_stm);
        result.i = result_after_exp.i; result.t = result_after_exp.t;
    }else{
        printf("Unsupported expression type.\n");
        exit(1);
    }

    return result;
}

int lookup(Table_ t, string key){
    Table_ current_table = t;
    while(current_table){
        if(current_table->id == key){
            return current_table->value;
        }
        current_table = current_table->tail;
    }
    printf("%s is used without declaration.\n", key);
    exit(1);
}

Table_ update(Table_ t, string key, int value){
    return Table(key, value, t);
}

void free_table(Table_ t){
    Table_ current = t;
    while(current){
        Table_ next = current->tail;
        free(current);
        current = next;
    }
}
