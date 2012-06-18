(* auto-generated by gt *)

open Subcore_util;;

(* This type is used for terminals.
We do this to have better position data.*)
type __terminal__ = (pd * string);;
type __term_not_in_ast__ = pd;;
type dummy = Dummy 
and binding = | Binding of pd * __terminal__ * __term_not_in_ast__ * oterm * __term_not_in_ast__ * oterm
and cmd = | Def of pd * __terminal__ * __term_not_in_ast__ * oterm * __term_not_in_ast__ * oterm | SetFlag of pd * __term_not_in_ast__ * __terminal__ | UnsetFlag of pd * __term_not_in_ast__ * __terminal__
and oterm = | Lam of pd * __term_not_in_ast__ * __terminal__ * __term_not_in_ast__ * oterm * __term_not_in_ast__ * oterm | Self of pd * __term_not_in_ast__ * __terminal__ * __term_not_in_ast__ * oterm | Fix of pd * __term_not_in_ast__ * binding * fix_oterm_comma0 * __term_not_in_ast__ * oterm | Arrow of pd * term * __term_not_in_ast__ * oterm | Pi of pd * __term_not_in_ast__ * __terminal__ * __term_not_in_ast__ * term * __term_not_in_ast__ * oterm | Check of pd * term * __term_not_in_ast__ * oterm | Term of pd * term
and prog = | Prog of pd * prog_prog_cmd1
and term = | App of pd * __term_not_in_ast__ * term * app_term_term2 * __term_not_in_ast__ | Star of pd * __term_not_in_ast__ | Var of pd * __terminal__ | Conv of pd * __term_not_in_ast__ * oterm * __term_not_in_ast__ * oterm * __term_not_in_ast__ * term * __term_not_in_ast__ * term | Trans of pd * __term_not_in_ast__ * oterm * trans_term_semi3 * __term_not_in_ast__ | Parens of pd * __term_not_in_ast__ * oterm * __term_not_in_ast__ | Fold of pd * __term_not_in_ast__ * __terminal__ | Unfold of pd * __term_not_in_ast__ | Eval of pd * __term_not_in_ast__ | Refl of pd * __term_not_in_ast__
and trans_term_semi3 = pd * ( __term_not_in_ast__ * oterm) list
and app_term_term2 = pd * ( term) list
and prog_prog_cmd1 = pd * ( cmd) list
and fix_oterm_comma0 = pd * ( __term_not_in_ast__ * binding) list;;

(* pd stands for pos (position) *)
let rec dummy () = () 
and get_terminal_pd = function
   | (pd,_) -> pd 
and get_term_pd_not_in_ast = function
   | (pd) -> pd 
and pd_binding = function 
  | Binding(pd,_,_,_,_,_) -> pd
and pd_cmd = function 
  | Def(pd,_,_,_,_,_) -> pd
  | SetFlag(pd,_,_) -> pd
  | UnsetFlag(pd,_,_) -> pd
and pd_oterm = function 
  | Lam(pd,_,_,_,_,_,_) -> pd
  | Self(pd,_,_,_,_) -> pd
  | Fix(pd,_,_,_,_,_) -> pd
  | Arrow(pd,_,_,_) -> pd
  | Pi(pd,_,_,_,_,_,_) -> pd
  | Check(pd,_,_,_) -> pd
  | Term(pd,_) -> pd
and pd_prog = function 
  | Prog(pd,_) -> pd
and pd_term = function 
  | App(pd,_,_,_,_) -> pd
  | Star(pd,_) -> pd
  | Var(pd,_) -> pd
  | Conv(pd,_,_,_,_,_,_,_,_) -> pd
  | Trans(pd,_,_,_,_) -> pd
  | Parens(pd,_,_,_) -> pd
  | Fold(pd,_,_) -> pd
  | Unfold(pd,_) -> pd
  | Eval(pd,_) -> pd
  | Refl(pd,_) -> pd
and pd_trans_term_semi3 = function 
  | (pd,[]) -> pd
  | (pd,(_,_)::___tail___) -> pd
and pd_app_term_term2 = function 
  | (pd,[]) -> pd
  | (pd,(_)::___tail___) -> pd
and pd_prog_prog_cmd1 = function 
  | (pd,[]) -> pd
  | (pd,(_)::___tail___) -> pd
and pd_fix_oterm_comma0 = function 
  | (pd,[]) -> pd
  | (pd,(_,_)::___tail___) -> pd;;
let pd e = pd_prog e;;