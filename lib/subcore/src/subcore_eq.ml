(* auto-generated by gt *)

open Subcore_syntax;;

let cur_line = ref 1;;
let rec print_new_line (os:string->unit) (do_print:bool) (p:int) : unit =
	if(p > !cur_line && do_print) then ( 
		os "\n"; 
		incr cur_line;
		print_new_line os do_print p;
	)
;;

let rec dummy () = () 
and pp_terminal (os:string->unit) (to_pretty_print:bool) = function 
	(d,str1) -> print_new_line os to_pretty_print (fst d); os str1

and eq_binding = function
   |Binding (d , str1_1 , pd2_1 , oterm3_1 , pd4_1 , oterm5_1),Binding (d' , str1_2 , pd2_2 , oterm3_2 , pd4_2 , oterm5_2)-> true && snd str1_1 = snd str1_2 && eq_oterm(oterm3_1 , oterm3_2) && eq_oterm(oterm5_1 , oterm5_2)

and eq_cmd = function
   |Def (d , pd1_1 , str2_1 , pd3_1 , oterm4_1 , pd5_1 , oterm6_1),Def (d' , pd1_2 , str2_2 , pd3_2 , oterm4_2 , pd5_2 , oterm6_2)-> true && snd str2_1 = snd str2_2 && eq_oterm(oterm4_1 , oterm4_2) && eq_oterm(oterm6_1 , oterm6_2)
   |SetFlag (d , pd1_1 , str2_1),SetFlag (d' , pd1_2 , str2_2)-> true && snd str2_1 = snd str2_2
   |UnsetFlag (d , pd1_1 , str2_1),UnsetFlag (d' , pd1_2 , str2_2)-> true && snd str2_1 = snd str2_2
   |ListFlags (d , pd1_1),ListFlags (d' , pd1_2)-> true
   |EvalCmd (d , pd1_1 , oterm2_1),EvalCmd (d' , pd1_2 , oterm2_2)-> true && eq_oterm(oterm2_1 , oterm2_2)
   |FixCmd (d , pd1_1 , binding2_1 , fixcmd_cmd_comma03_1),FixCmd (d' , pd1_2 , binding2_2 , fixcmd_cmd_comma03_2)-> true && eq_binding(binding2_1 , binding2_2) && eq_fixcmd_cmd_comma0(fixcmd_cmd_comma03_1 , fixcmd_cmd_comma03_2)
   | _ -> false


and eq_colon = function
   |Colon (d , pd1_1),Colon (d' , pd1_2)-> true
   |Dcolon (d , pd1_1),Dcolon (d' , pd1_2)-> true
   | _ -> false


and eq_oterm = function
   |Lam (d , pd1_1 , str2_1 , colon3_1 , oterm4_1 , pd5_1 , oterm6_1),Lam (d' , pd1_2 , str2_2 , colon3_2 , oterm4_2 , pd5_2 , oterm6_2)-> true && snd str2_1 = snd str2_2 && eq_colon(colon3_1 , colon3_2) && eq_oterm(oterm4_1 , oterm4_2) && eq_oterm(oterm6_1 , oterm6_2)
   |Self (d , pd1_1 , str2_1 , pd3_1 , oterm4_1),Self (d' , pd1_2 , str2_2 , pd3_2 , oterm4_2)-> true && snd str2_1 = snd str2_2 && eq_oterm(oterm4_1 , oterm4_2)
   |Fix (d , pd1_1 , binding2_1 , fix_oterm_comma13_1 , pd4_1 , oterm5_1),Fix (d' , pd1_2 , binding2_2 , fix_oterm_comma13_2 , pd4_2 , oterm5_2)-> true && eq_binding(binding2_1 , binding2_2) && eq_fix_oterm_comma1(fix_oterm_comma13_1 , fix_oterm_comma13_2) && eq_oterm(oterm5_1 , oterm5_2)
   |Let (d , pd1_1 , str2_1 , pd3_1 , term4_1 , pd5_1 , term6_1 , pd7_1 , oterm8_1),Let (d' , pd1_2 , str2_2 , pd3_2 , term4_2 , pd5_2 , term6_2 , pd7_2 , oterm8_2)-> true && snd str2_1 = snd str2_2 && eq_term(term4_1 , term4_2) && eq_term(term6_1 , term6_2) && eq_oterm(oterm8_1 , oterm8_2)
   |CbvArrow (d , term1_1 , pd2_1 , oterm3_1),CbvArrow (d' , term1_2 , pd2_2 , oterm3_2)-> true && eq_term(term1_1 , term1_2) && eq_oterm(oterm3_1 , oterm3_2)
   |CbnArrow (d , term1_1 , pd2_1 , oterm3_1),CbnArrow (d' , term1_2 , pd2_2 , oterm3_2)-> true && eq_term(term1_1 , term1_2) && eq_oterm(oterm3_1 , oterm3_2)
   |Pi (d , pd1_1 , str2_1 , colon3_1 , term4_1 , pd5_1 , oterm6_1),Pi (d' , pd1_2 , str2_2 , colon3_2 , term4_2 , pd5_2 , oterm6_2)-> true && snd str2_1 = snd str2_2 && eq_colon(colon3_1 , colon3_2) && eq_term(term4_1 , term4_2) && eq_oterm(oterm6_1 , oterm6_2)
   |Check (d , term1_1 , pd2_1 , oterm3_1),Check (d' , term1_2 , pd2_2 , oterm3_2)-> true && eq_term(term1_1 , term1_2) && eq_oterm(oterm3_1 , oterm3_2)
   |Term (d , term1_1),Term (d' , term1_2)-> true && eq_term(term1_1 , term1_2)
   | _ -> false


and eq_prog = function
   |Prog (d , prog_prog_cmd21_1),Prog (d' , prog_prog_cmd21_2)-> true && eq_prog_prog_cmd2(prog_prog_cmd21_1 , prog_prog_cmd21_2)

and eq_term = function
   |App (d , pd1_1 , term2_1 , app_term_term33_1 , pd4_1),App (d' , pd1_2 , term2_2 , app_term_term33_2 , pd4_2)-> true && eq_term(term2_1 , term2_2) && eq_app_term_term3(app_term_term33_1 , app_term_term33_2)
   |Star (d , pd1_1),Star (d' , pd1_2)-> true
   |Var (d , str1_1),Var (d' , str1_2)-> true && snd str1_1 = snd str1_2
   |Conv (d , pd1_1 , oterm2_1 , pd3_1 , oterm4_1 , pd5_1 , term6_1 , pd7_1 , term8_1),Conv (d' , pd1_2 , oterm2_2 , pd3_2 , oterm4_2 , pd5_2 , term6_2 , pd7_2 , term8_2)-> true && eq_oterm(oterm2_1 , oterm2_2) && eq_oterm(oterm4_1 , oterm4_2) && eq_term(term6_1 , term6_2) && eq_term(term8_1 , term8_2)
   |Trans (d , pd1_1 , oterm2_1 , trans_term_semi43_1 , pd4_1),Trans (d' , pd1_2 , oterm2_2 , trans_term_semi43_2 , pd4_2)-> true && eq_oterm(oterm2_1 , oterm2_2) && eq_trans_term_semi4(trans_term_semi43_1 , trans_term_semi43_2)
   |Parens (d , pd1_1 , oterm2_1 , pd3_1),Parens (d' , pd1_2 , oterm2_2 , pd3_2)-> true && eq_oterm(oterm2_1 , oterm2_2)
   |Substself (d , pd1_1),Substself (d' , pd1_2)-> true
   |Unfold (d , pd1_1),Unfold (d' , pd1_2)-> true
   |Eval (d , pd1_1 , eval_term_la52_1),Eval (d' , pd1_2 , eval_term_la52_2)-> true && eq_eval_term_la5(eval_term_la52_1 , eval_term_la52_2)
   |Refl (d , pd1_1),Refl (d' , pd1_2)-> true
   | _ -> false


and eq_eval_term_la5 = function
   | (_,None), (_,None)-> true
   | (d , Some(pd1_1 , pd2_1 , pd3_1)), (d' , Some(pd1_2 , pd2_2 , pd3_2))-> true
   | _ -> false


and eq_trans_term_semi4 = function
   |(_,[]),(_,[])-> true
   | (d , (pd1_1 , oterm2_1)::trans_term_semi43_1), (d' , (pd1_2 , oterm2_2)::trans_term_semi43_2)-> true && eq_oterm(oterm2_1 , oterm2_2) && eq_trans_term_semi4((d,trans_term_semi43_1) , (d',trans_term_semi43_2))
   | _ -> false


and eq_app_term_term3 = function
   |(_,[]),(_,[])-> true
   | (d , (term1_1)::app_term_term32_1), (d' , (term1_2)::app_term_term32_2)-> true && eq_term(term1_1 , term1_2) && eq_app_term_term3((d,app_term_term32_1) , (d',app_term_term32_2))
   | _ -> false


and eq_prog_prog_cmd2 = function
   |(_,[]),(_,[])-> true
   | (d , (cmd1_1)::prog_prog_cmd22_1), (d' , (cmd1_2)::prog_prog_cmd22_2)-> true && eq_cmd(cmd1_1 , cmd1_2) && eq_prog_prog_cmd2((d,prog_prog_cmd22_1) , (d',prog_prog_cmd22_2))
   | _ -> false


and eq_fix_oterm_comma1 = function
   |(_,[]),(_,[])-> true
   | (d , (pd1_1 , binding2_1)::fix_oterm_comma13_1), (d' , (pd1_2 , binding2_2)::fix_oterm_comma13_2)-> true && eq_binding(binding2_1 , binding2_2) && eq_fix_oterm_comma1((d,fix_oterm_comma13_1) , (d',fix_oterm_comma13_2))
   | _ -> false


and eq_fixcmd_cmd_comma0 = function
   |(_,[]),(_,[])-> true
   | (d , (pd1_1 , binding2_1)::fixcmd_cmd_comma03_1), (d' , (pd1_2 , binding2_2)::fixcmd_cmd_comma03_2)-> true && eq_binding(binding2_1 , binding2_2) && eq_fixcmd_cmd_comma0((d,fixcmd_cmd_comma03_1) , (d',fixcmd_cmd_comma03_2))
   | _ -> false
;;

let eq e = eq_prog e;;