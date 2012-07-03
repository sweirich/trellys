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

and pp_binding (os:string->unit) (to_pretty_print:bool) = function 
   |Binding (d , str1 , pd2 , oterm3 , pd4 , oterm5) -> print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str1; os " " ;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd2); os ":"; os " " ;pp_oterm os to_pretty_print oterm3;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd4); os "="; os " " ;pp_oterm os to_pretty_print oterm5; () 

and pp_cmd (os:string->unit) (to_pretty_print:bool) = function 
   |Def (d , pd1 , str2 , pd3 , oterm4 , pd5 , oterm6) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "Define"; os " " ;print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str2; os " " ;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd3); os ":"; os " " ;pp_oterm os to_pretty_print oterm4;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd5); os "="; os " " ;pp_oterm os to_pretty_print oterm6; () 
   |SetFlag (d , pd1 , str2) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "Set"; os " " ;print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str2; os " " ; () 
   |UnsetFlag (d , pd1 , str2) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "Unset"; os " " ;print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str2; os " " ; () 
   |ListFlags (d , pd1) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "ListFlags"; os " " ; () 
   |EvalCmd (d , pd1 , oterm2) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "Eval"; os " " ;pp_oterm os to_pretty_print oterm2; () 
   |FixCmd (d , pd1 , binding2 , fixcmd_cmd_comma03) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "Fix"; os " " ;pp_binding os to_pretty_print binding2;pp_fixcmd_cmd_comma0 os to_pretty_print fixcmd_cmd_comma03; () 

and pp_colon (os:string->unit) (to_pretty_print:bool) = function 
   |Colon (d , pd1) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os ":"; os " " ; () 
   |Dcolon (d , pd1) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "::"; os " " ; () 

and pp_oterm (os:string->unit) (to_pretty_print:bool) = function 
   |Lam (d , pd1 , str2 , colon3 , oterm4 , pd5 , oterm6) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "\\"; os " " ;print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str2; os " " ;pp_colon os to_pretty_print colon3;pp_oterm os to_pretty_print oterm4;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd5); os "."; os " " ;pp_oterm os to_pretty_print oterm6; () 
   |Self (d , pd1 , str2 , pd3 , oterm4) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "self"; os " " ;print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str2; os " " ;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd3); os "."; os " " ;pp_oterm os to_pretty_print oterm4; () 
   |Fix (d , pd1 , binding2 , fix_oterm_comma13 , pd4 , oterm5) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "fix"; os " " ;pp_binding os to_pretty_print binding2;pp_fix_oterm_comma1 os to_pretty_print fix_oterm_comma13;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd4); os "in"; os " " ;pp_oterm os to_pretty_print oterm5; () 
   |CbvArrow (d , term1 , pd2 , oterm3) -> pp_term os to_pretty_print term1;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd2); os "->"; os " " ;pp_oterm os to_pretty_print oterm3; () 
   |CbnArrow (d , term1 , pd2 , oterm3) -> pp_term os to_pretty_print term1;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd2); os "=>"; os " " ;pp_oterm os to_pretty_print oterm3; () 
   |Pi (d , pd1 , str2 , colon3 , term4 , pd5 , oterm6) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "!"; os " " ;print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str2; os " " ;pp_colon os to_pretty_print colon3;pp_term os to_pretty_print term4;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd5); os "."; os " " ;pp_oterm os to_pretty_print oterm6; () 
   |Check (d , term1 , pd2 , oterm3) -> pp_term os to_pretty_print term1;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd2); os ":"; os " " ;pp_oterm os to_pretty_print oterm3; () 
   |Term (d , term1) -> pp_term os to_pretty_print term1; () 

and pp_prog (os:string->unit) (to_pretty_print:bool) = function 
   |Prog (d , prog_prog_cmd21) -> pp_prog_prog_cmd2 os to_pretty_print prog_prog_cmd21; () 

and pp_term (os:string->unit) (to_pretty_print:bool) = function 
   |App (d , pd1 , term2 , app_term_term33 , pd4) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "("; os " " ;pp_term os to_pretty_print term2;pp_app_term_term3 os to_pretty_print app_term_term33;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd4); os ")"; os " " ; () 
   |Star (d , pd1) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "*"; os " " ; () 
   |Var (d , str1) -> print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str1; os " " ; () 
   |Conv (d , pd1 , oterm2 , pd3 , oterm4 , pd5 , term6 , pd7 , term8) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "conv"; os " " ;pp_oterm os to_pretty_print oterm2;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd3); os "to"; os " " ;pp_oterm os to_pretty_print oterm4;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd5); os "by"; os " " ;pp_term os to_pretty_print term6;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd7); os ","; os " " ;pp_term os to_pretty_print term8; () 
   |Trans (d , pd1 , oterm2 , trans_term_semi43 , pd4) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "["; os " " ;pp_oterm os to_pretty_print oterm2;pp_trans_term_semi4 os to_pretty_print trans_term_semi43;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd4); os "]"; os " " ; () 
   |Parens (d , pd1 , oterm2 , pd3) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "("; os " " ;pp_oterm os to_pretty_print oterm2;print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd3); os ")"; os " " ; () 
   |Substself (d , pd1) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "substself"; os " " ; () 
   |Unfold (d , pd1) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "unfold"; os " " ; () 
   |Eval (d , pd1) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "eval"; os " " ; () 
   |Refl (d , pd1) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os "refl"; os " " ; () 

and pp_trans_term_semi4 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,[]) ->  () 
   | (d , (pd1 , oterm2)::trans_term_semi43) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os ";"; os " " ;pp_oterm os to_pretty_print oterm2;pp_trans_term_semi4 os to_pretty_print  (d,trans_term_semi43); () 

and pp_app_term_term3 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,[]) ->  () 
   | (d , (term1)::app_term_term32) -> pp_term os to_pretty_print term1;pp_app_term_term3 os to_pretty_print  (d,app_term_term32); () 

and pp_prog_prog_cmd2 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,[]) ->  () 
   | (d , (cmd1)::prog_prog_cmd22) -> pp_cmd os to_pretty_print cmd1;pp_prog_prog_cmd2 os to_pretty_print  (d,prog_prog_cmd22); () 

and pp_fix_oterm_comma1 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,[]) ->  () 
   | (d , (pd1 , binding2)::fix_oterm_comma13) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os ","; os " " ;pp_binding os to_pretty_print binding2;pp_fix_oterm_comma1 os to_pretty_print  (d,fix_oterm_comma13); () 

and pp_fixcmd_cmd_comma0 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,[]) ->  () 
   | (d , (pd1 , binding2)::fixcmd_cmd_comma03) -> print_new_line os to_pretty_print (fst d); print_new_line os to_pretty_print (fst pd1); os ","; os " " ;pp_binding os to_pretty_print binding2;pp_fixcmd_cmd_comma0 os to_pretty_print  (d,fixcmd_cmd_comma03); () ;;

let pp (os:string->unit) (to_pretty_print:bool) e = pp_prog os to_pretty_print e;;