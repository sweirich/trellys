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

and ppast_binding (os:string->unit) (to_pretty_print:bool) = function 
   |Binding (d , str1 , pd2 , oterm3 , pd4 , oterm5) ->  os "Binding"; os "("; print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str1; os "";os ","; print_new_line os to_pretty_print (fst pd2); os "COLON("; os "\""; os ":"; os "\")"; os "";os ","; ppast_oterm os to_pretty_print oterm3; os "";os ","; print_new_line os to_pretty_print (fst pd4); os "EQ("; os "\""; os "="; os "\")"; os "";os ","; ppast_oterm os to_pretty_print oterm5; os "";os ")";  () 

and ppast_cmd (os:string->unit) (to_pretty_print:bool) = function 
   |Def (d , str1 , pd2 , oterm3 , pd4 , oterm5) ->  os "Def"; os "("; print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str1; os "";os ","; print_new_line os to_pretty_print (fst pd2); os "COLON("; os "\""; os ":"; os "\")"; os "";os ","; ppast_oterm os to_pretty_print oterm3; os "";os ","; print_new_line os to_pretty_print (fst pd4); os "EQ("; os "\""; os "="; os "\")"; os "";os ","; ppast_oterm os to_pretty_print oterm5; os "";os ")";  () 
   |SetFlag (d , pd1 , str2) ->  os "SetFlag"; os "(";print_new_line os to_pretty_print (fst pd1); os "SET("; os "\""; os "Set"; os "\")"; os "";os ",";  print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str2; os "";os ")";  () 
   |UnsetFlag (d , pd1 , str2) ->  os "UnsetFlag"; os "(";print_new_line os to_pretty_print (fst pd1); os "UNSET("; os "\""; os "Unset"; os "\")"; os "";os ",";  print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str2; os "";os ")";  () 

and ppast_oterm (os:string->unit) (to_pretty_print:bool) = function 
   |Lam (d , pd1 , str2 , pd3 , oterm4 , pd5 , oterm6) ->  os "Lam"; os "(";print_new_line os to_pretty_print (fst pd1); os "LAM("; os "\""; os "\\"; os "\")"; os "";os ",";  print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str2; os "";os ","; print_new_line os to_pretty_print (fst pd3); os "COLON("; os "\""; os ":"; os "\")"; os "";os ","; ppast_oterm os to_pretty_print oterm4; os "";os ","; print_new_line os to_pretty_print (fst pd5); os "DOT("; os "\""; os "."; os "\")"; os "";os ","; ppast_oterm os to_pretty_print oterm6; os "";os ")";  () 
   |Self (d , pd1 , str2 , pd3 , oterm4) ->  os "Self"; os "(";print_new_line os to_pretty_print (fst pd1); os "SELF("; os "\""; os "self"; os "\")"; os "";os ",";  print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str2; os "";os ","; print_new_line os to_pretty_print (fst pd3); os "DOT("; os "\""; os "."; os "\")"; os "";os ","; ppast_oterm os to_pretty_print oterm4; os "";os ")";  () 
   |Fix (d , pd1 , binding2 , fix_oterm_comma03 , pd4 , oterm5) ->  os "Fix"; os "(";print_new_line os to_pretty_print (fst pd1); os "FIX("; os "\""; os "fix"; os "\")"; os "";os ","; ppast_binding os to_pretty_print binding2; os "";os ","; ppast_fix_oterm_comma0 os to_pretty_print fix_oterm_comma03; os "";os ","; print_new_line os to_pretty_print (fst pd4); os "IN("; os "\""; os "in"; os "\")"; os "";os ","; ppast_oterm os to_pretty_print oterm5; os "";os ")";  () 
   |Arrow (d , term1 , pd2 , oterm3) ->  os "Arrow"; os "(";ppast_term os to_pretty_print term1; os "";os ","; print_new_line os to_pretty_print (fst pd2); os "ARROW("; os "\""; os "->"; os "\")"; os "";os ","; ppast_oterm os to_pretty_print oterm3; os "";os ")";  () 
   |Pi (d , pd1 , str2 , pd3 , term4 , pd5 , oterm6) ->  os "Pi"; os "(";print_new_line os to_pretty_print (fst pd1); os "PI("; os "\""; os "!"; os "\")"; os "";os ",";  print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str2; os "";os ","; print_new_line os to_pretty_print (fst pd3); os "COLON("; os "\""; os ":"; os "\")"; os "";os ","; ppast_term os to_pretty_print term4; os "";os ","; print_new_line os to_pretty_print (fst pd5); os "DOT("; os "\""; os "."; os "\")"; os "";os ","; ppast_oterm os to_pretty_print oterm6; os "";os ")";  () 
   |Check (d , term1 , pd2 , oterm3) ->  os "Check"; os "(";ppast_term os to_pretty_print term1; os "";os ","; print_new_line os to_pretty_print (fst pd2); os "COLON("; os "\""; os ":"; os "\")"; os "";os ","; ppast_oterm os to_pretty_print oterm3; os "";os ")";  () 
   |Term (d , term1) ->  os "Term"; os "(";ppast_term os to_pretty_print term1; os "";os ")";  () 

and ppast_prog (os:string->unit) (to_pretty_print:bool) = function 
   |Prog (d , prog_prog_cmd11) ->  os "Prog"; os "(";ppast_prog_prog_cmd1 os to_pretty_print prog_prog_cmd11; os "";os ")";  () 

and ppast_term (os:string->unit) (to_pretty_print:bool) = function 
   |App (d , pd1 , term2 , app_term_term23 , pd4) ->  os "App"; os "(";print_new_line os to_pretty_print (fst pd1); os "LP("; os "\""; os "("; os "\")"; os "";os ","; ppast_term os to_pretty_print term2; os "";os ","; ppast_app_term_term2 os to_pretty_print app_term_term23; os "";os ","; print_new_line os to_pretty_print (fst pd4); os "RP("; os "\""; os ")"; os "\")"; os "";os ")";  () 
   |Star (d , pd1) ->  os "Star"; os "(";print_new_line os to_pretty_print (fst pd1); os "STAR("; os "\""; os "*"; os "\")"; os "";os ")";  () 
   |Var (d , str1) ->  os "Var"; os "("; print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str1; os "";os ")";  () 
   |Conv (d , pd1 , oterm2 , pd3 , oterm4 , pd5 , term6 , pd7 , term8) ->  os "Conv"; os "(";print_new_line os to_pretty_print (fst pd1); os "CONV("; os "\""; os "conv"; os "\")"; os "";os ","; ppast_oterm os to_pretty_print oterm2; os "";os ","; print_new_line os to_pretty_print (fst pd3); os "TO("; os "\""; os "to"; os "\")"; os "";os ","; ppast_oterm os to_pretty_print oterm4; os "";os ","; print_new_line os to_pretty_print (fst pd5); os "BY("; os "\""; os "by"; os "\")"; os "";os ","; ppast_term os to_pretty_print term6; os "";os ","; print_new_line os to_pretty_print (fst pd7); os "COMMA("; os "\""; os ","; os "\")"; os "";os ","; ppast_term os to_pretty_print term8; os "";os ")";  () 
   |Trans (d , pd1 , oterm2 , trans_term_semi33 , pd4) ->  os "Trans"; os "(";print_new_line os to_pretty_print (fst pd1); os "LS("; os "\""; os "["; os "\")"; os "";os ","; ppast_oterm os to_pretty_print oterm2; os "";os ","; ppast_trans_term_semi3 os to_pretty_print trans_term_semi33; os "";os ","; print_new_line os to_pretty_print (fst pd4); os "RS("; os "\""; os "]"; os "\")"; os "";os ")";  () 
   |Parens (d , pd1 , oterm2 , pd3) ->  os "Parens"; os "(";print_new_line os to_pretty_print (fst pd1); os "LP("; os "\""; os "("; os "\")"; os "";os ","; ppast_oterm os to_pretty_print oterm2; os "";os ","; print_new_line os to_pretty_print (fst pd3); os "RP("; os "\""; os ")"; os "\")"; os "";os ")";  () 
   |Fold (d , pd1 , str2) ->  os "Fold"; os "(";print_new_line os to_pretty_print (fst pd1); os "FOLD("; os "\""; os "fold"; os "\")"; os "";os ",";  print_new_line os to_pretty_print (fst d);  pp_terminal os to_pretty_print str2; os "";os ")";  () 
   |Substself (d , pd1) ->  os "Substself"; os "(";print_new_line os to_pretty_print (fst pd1); os "SUBSTSELF("; os "\""; os "substself"; os "\")"; os "";os ")";  () 
   |Unfold (d , pd1) ->  os "Unfold"; os "(";print_new_line os to_pretty_print (fst pd1); os "UNFOLD("; os "\""; os "unfold"; os "\")"; os "";os ")";  () 
   |Eval (d , pd1) ->  os "Eval"; os "(";print_new_line os to_pretty_print (fst pd1); os "EVAL("; os "\""; os "eval"; os "\")"; os "";os ")";  () 
   |Refl (d , pd1) ->  os "Refl"; os "(";print_new_line os to_pretty_print (fst pd1); os "REFL("; os "\""; os "refl"; os "\")"; os "";os ")";  () 

and ppast_trans_term_semi3 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,[]) ->  os "[";  os "]"; os ")";  () 
   | (d , (pd1 , oterm2)::trans_term_semi33) ->  os "["; print_new_line os to_pretty_print (fst pd1); os "SEMI("; os "\""; os ";"; os "\")"; os "";os ";"; ppast_oterm os to_pretty_print oterm2; os "";os ";"; ppast_trans_term_semi3 os to_pretty_print (d,trans_term_semi33); os ""; os "]"; os ")";  () 

and ppast_app_term_term2 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,[]) ->  os "[";  os "]"; os ")";  () 
   | (d , (term1)::app_term_term22) ->  os "["; ppast_term os to_pretty_print term1; os "";os ";"; ppast_app_term_term2 os to_pretty_print (d,app_term_term22); os ""; os "]"; os ")";  () 

and ppast_prog_prog_cmd1 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,[]) ->  os "[";  os "]"; os ")";  () 
   | (d , (cmd1)::prog_prog_cmd12) ->  os "["; ppast_cmd os to_pretty_print cmd1; os "";os ";"; ppast_prog_prog_cmd1 os to_pretty_print (d,prog_prog_cmd12); os ""; os "]"; os ")";  () 

and ppast_fix_oterm_comma0 (os:string->unit) (to_pretty_print:bool) = function 
   | (d,[]) ->  os "[";  os "]"; os ")";  () 
   | (d , (pd1 , binding2)::fix_oterm_comma03) ->  os "["; print_new_line os to_pretty_print (fst pd1); os "COMMA("; os "\""; os ","; os "\")"; os "";os ";"; ppast_binding os to_pretty_print binding2; os "";os ";"; ppast_fix_oterm_comma0 os to_pretty_print (d,fix_oterm_comma03); os ""; os "]"; os ")";  () ;;

let ppast (os:string->unit) (to_pretty_print:bool) e = ppast_prog os to_pretty_print e;;