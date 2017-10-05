%{
/* Lab2 Attention: You are only allowed to add code in this file and start at Line 26.*/
#include <string.h>
#include "util.h"
#include "symbol.h"
#include "errormsg.h"
#include "absyn.h"
#include "y.tab.h"

int charPos=1;

int yywrap(void)
{
 charPos=1;
 return 1;
}

void adjust(void)
{
 EM_tokPos=charPos;
 charPos+=yyleng;
}

/*
* Please don't modify the lines above.
* You can add C declarations of your own below.
*/

#define MAX_STR_LEN 4096
int comment_stack = 0;
char str_buf[MAX_STR_LEN];
int str_len = 0;

void adjust_str()
{
  charPos += yyleng;
}
/* @function: getstr
 * @input: a string literal
 * @output: the string value for the input which has all the escape sequences 
 * translated into their meaning.
 */
char *getstr(const char *str)
{
	//optional: implement this function if you need it
	return NULL;
}

%}
  /* You can add lex definitions here. */

ID [a-zA-Z][a-zA-Z0-9_]*
INT [0-9]+
DIGITS [0-9][0-9][0-9]

%Start COMMENT STR
%%
  /* 
  * Below is an example, which you can wipe out
  * and write reguler expressions and actions of your own.
  */ 
<INITIAL>"\n" {adjust(); EM_newline(); continue;}
<INITIAL>"\t" {adjust(); continue;}
<INITIAL>" " {adjust(); continue;}

<INITIAL>"array" {adjust(); return ARRAY;}
<INITIAL>"if" {adjust(); return IF;}
<INITIAL>"then" {adjust(); return THEN;}
<INITIAL>"else" {adjust(); return ELSE;}
<INITIAL>"while" {adjust(); return WHILE;}
<INITIAL>"for" {adjust() ; return FOR;}
<INITIAL>"to" {adjust(); return TO;}
<INITIAL>"do" {adjust(); return DO;}
<INITIAL>"let" {adjust(); return LET;}
<INITIAL>"in" {adjust(); return IN;}
<INITIAL>"end" {adjust(); return END;}
<INITIAL>"of" {adjust(); return OF;}
<INITIAL>"break" {adjust(); return BREAK;}
<INITIAL>"nil" {adjust(); return NIL;}
<INITIAL>"function" {adjust(); return FUNCTION;}
<INITIAL>"var" {adjust(); return VAR;}
<INITIAL>"type" {adjust(); return TYPE;}

<INITIAL>"," {adjust(); return COMMA;}
<INITIAL>":" {adjust(); return COLON;}
<INITIAL>";" {adjust(); return SEMICOLON;}
<INITIAL>"(" {adjust(); return LPAREN;}
<INITIAL>")" {adjust(); return RPAREN;}
<INITIAL>"[" {adjust(); return LBRACK;}
<INITIAL>"]" {adjust(); return RBRACK;}
<INITIAL>"{" {adjust(); return LBRACE;}
<INITIAL>"}" {adjust(); return RBRACE;}
<INITIAL>"." {adjust(); return DOT;}
<INITIAL>"+" {adjust(); return PLUS;}
<INITIAL>"-" {adjust(); return MINUS;}
<INITIAL>"*" {adjust(); return TIMES;}
<INITIAL>"/" {adjust(); return DIVIDE;}
<INITIAL>"=" {adjust(); return EQ;}
<INITIAL>"<>" {adjust(); return NEQ;}
<INITIAL>"<" {adjust(); return LT;}
<INITIAL>"<=" {adjust(); return LE;}
<INITIAL>">" {adjust(); return GT;}
<INITIAL>">=" {adjust(); return GE;}
<INITIAL>"&" {adjust(); return AND;}
<INITIAL>"|" {adjust(); return OR;}
<INITIAL>":=" {adjust(); return ASSIGN;}

<INITIAL>{ID} {adjust(); yylval.sval=String(yytext); return ID;}
<INITIAL>{INT} {adjust(); yylval.ival=atoi(yytext); return INT;}

<INITIAL>\" {adjust(); strcpy(str_buf, "\0"); BEGIN STR;}
<INITIAL>"/*" {adjust(); comment_stack = 0; comment_stack++; BEGIN COMMENT;}

<INITIAL>. {adjust(); EM_error(EM_tokPos, "Illegal token");}
<INITIAL><<EOF>> {adjust(); yyterminate();}

<STR>\\n {adjust_str(); strcat(str_buf, "\n");}
<STR>\\t {adjust_str(); strcat(str_buf, "\t");}
<STR>\\\^[@A-Z\[\\\]\^_] {adjust_str(); strcat(str_buf, yytext);}
<STR>\\{DIGITS} {
  adjust_str();
  str_len = strlen(str_buf);
  str_buf[str_len] = atoi(yytext + 1);
  str_buf[str_len + 1] = '\0'; 
}
<STR>\\\" {adjust_str(); strcat(str_buf, "\"");}
<STR>\\\\ {adjust_str(); strcat(str_buf, "\\");}
<STR>\\[ \t\n\f]+\\ {adjust_str();}
<STR>\" {adjust_str(); BEGIN INITIAL; yylval.sval = String(str_buf); return STRING;}
<STR>\\ {adjust_str(); EM_error(EM_tokPos, "Illegal escaped character");}
<STR>. {adjust_str(); strcat(str_buf, yytext);}
<STR><<EOF>> {adjust_str(); EM_error(EM_tokPos, "Expect \" at the end of a string");}

<COMMENT>"/*" {adjust(); comment_stack++;}
<COMMENT>. {adjust(); continue;}
<COMMENT>\n {adjust(); EM_newline();}
<COMMENT>"*/" {
  adjust();
  comment_stack--;
  if(comment_stack == 0) BEGIN INITIAL;
}
<COMMENT><<EOF>> {adjust(); EM_error(EM_tokPos, "Expect */ at the end of a comment");}

