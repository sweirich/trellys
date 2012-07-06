%{
(* auto-generated by gt *)

   open Subcore_syntax;;
let parse_error s =
	 let error = s^(Subcore_util.string_of_pos (Subcore_util.cur_pd())) in failwith error;;

%}

%start main

%token EOF
%token <Subcore_syntax.__term_not_in_ast__> DOT DEFINE IN CONV PI REFL EVALCMD LAM COMMA TO EQ LS SEMI LP SUBSTSELF COLON FIX EVAL LA STAR SELF RS FATARROW RP ARROW UNFOLD LISTFLAGS DCOLON FIXCMD BY RA SET UNSET
%token <Subcore_syntax.__terminal__> ID

%type <Subcore_syntax.prog option> main
%type <Subcore_syntax.binding> binding
%type <Subcore_syntax.cmd> cmd
%type <Subcore_syntax.colon> colon
%type <Subcore_syntax.prog> prog
%type <Subcore_syntax.oterm> oterm
%type <Subcore_syntax.trans_term_semi4> trans_term_semi4
%type <Subcore_syntax.term> term
%type <Subcore_syntax.prog_prog_cmd2> prog_prog_cmd2
%type <Subcore_syntax.eval_term_la5> eval_term_la5
%type <Subcore_syntax.app_term_term3> app_term_term3
%type <Subcore_syntax.fix_oterm_comma1> fix_oterm_comma1
%type <Subcore_syntax.fixcmd_cmd_comma0> fixcmd_cmd_comma0
%type <Subcore_util.pd> cur_position

%%



main:
	| prog { Some($1) }
	| EOF { None }



cur_position:
| { Subcore_util.cur_pd() }

binding:
  | ID COLON oterm EQ oterm { Binding(get_terminal_pd $1, $1, $2, $3, $4, $5) }

cmd:
  | DEFINE ID COLON oterm EQ oterm { Def(get_term_pd_not_in_ast $1, $1, $2, $3, $4, $5, $6) }

cmd:
  | SET ID { SetFlag(get_term_pd_not_in_ast $1, $1, $2) }

cmd:
  | UNSET ID { UnsetFlag(get_term_pd_not_in_ast $1, $1, $2) }

cmd:
  | LISTFLAGS { ListFlags(get_term_pd_not_in_ast $1, $1) }

cmd:
  | EVALCMD oterm { EvalCmd(get_term_pd_not_in_ast $1, $1, $2) }

cmd:
  | FIXCMD binding fixcmd_cmd_comma0 { FixCmd(get_term_pd_not_in_ast $1, $1, $2, $3) }

colon:
  | COLON { Colon(get_term_pd_not_in_ast $1, $1) }

colon:
  | DCOLON { Dcolon(get_term_pd_not_in_ast $1, $1) }

oterm:
  | LAM ID colon oterm DOT oterm { Lam(get_term_pd_not_in_ast $1, $1, $2, $3, $4, $5, $6) }

oterm:
  | SELF ID DOT oterm { Self(get_term_pd_not_in_ast $1, $1, $2, $3, $4) }

oterm:
  | FIX binding fix_oterm_comma1 IN oterm { Fix(get_term_pd_not_in_ast $1, $1, $2, $3, $4, $5) }

oterm:
  | term ARROW oterm { CbvArrow(pd_term $1, $1, $2, $3) }

oterm:
  | term FATARROW oterm { CbnArrow(pd_term $1, $1, $2, $3) }

oterm:
  | PI ID colon term DOT oterm { Pi(get_term_pd_not_in_ast $1, $1, $2, $3, $4, $5, $6) }

oterm:
  | term COLON oterm { Check(pd_term $1, $1, $2, $3) }

oterm:
  | term { Term(pd_term $1, $1) }

prog:
  | prog_prog_cmd2 { Prog(pd_prog_prog_cmd2 $1, $1) }

term:
  | LP term app_term_term3 RP { App(get_term_pd_not_in_ast $1, $1, $2, $3, $4) }

term:
  | STAR { Star(get_term_pd_not_in_ast $1, $1) }

term:
  | ID { Var(get_terminal_pd $1, $1) }

term:
  | CONV oterm TO oterm BY term COMMA term { Conv(get_term_pd_not_in_ast $1, $1, $2, $3, $4, $5, $6, $7, $8) }

term:
  | LS oterm trans_term_semi4 RS { Trans(get_term_pd_not_in_ast $1, $1, $2, $3, $4) }

term:
  | LP oterm RP { Parens(get_term_pd_not_in_ast $1, $1, $2, $3) }

term:
  | SUBSTSELF { Substself(get_term_pd_not_in_ast $1, $1) }

term:
  | UNFOLD { Unfold(get_term_pd_not_in_ast $1, $1) }

term:
  | EVAL eval_term_la5 { Eval(get_term_pd_not_in_ast $1, $1, $2) }

term:
  | REFL { Refl(get_term_pd_not_in_ast $1, $1) }

eval_term_la5:
  | cur_position { ($1, None) }

eval_term_la5:
  | LA UNFOLD RA { (get_term_pd_not_in_ast $1, Some( $1 , $2, $3)) }

trans_term_semi4:
  | SEMI oterm { (get_term_pd_not_in_ast $1, ($1, $2)::[]) }

trans_term_semi4:
  | SEMI oterm trans_term_semi4 { (get_term_pd_not_in_ast $1, ($1, $2)::(snd $3)) }

app_term_term3:
  | term { (pd_term $1, ($1)::[]) }

app_term_term3:
  | term app_term_term3 { (pd_term $1, ($1)::(snd $2)) }

prog_prog_cmd2:
  | cmd { (pd_cmd $1, ($1)::[]) }

prog_prog_cmd2:
  | cmd prog_prog_cmd2 { (pd_cmd $1, ($1)::(snd $2)) }

fix_oterm_comma1:
  | cur_position { ($1, []) }

fix_oterm_comma1:
  | COMMA binding fix_oterm_comma1 { (get_term_pd_not_in_ast $1, ($1, $2)::(snd $3)) }

fixcmd_cmd_comma0:
  | cur_position { ($1, []) }

fixcmd_cmd_comma0:
  | COMMA binding fixcmd_cmd_comma0 { (get_term_pd_not_in_ast $1, ($1, $2)::(snd $3)) }
