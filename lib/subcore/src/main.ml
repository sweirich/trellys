open Subcore_util;;
open Trie;;

(***********************************************************************)
(* Abstract syntax *)

type binder = Pi | Lam

type strategy = Cbv | Cbn

type term = 
    App of term * term
  | Binder of binder * string * strategy * term * term
  | Fix of binding list * term
  | Arrow of term * strategy * term
  | Var of string
  | Self of string * term
  | Star
  | Check of term * term
  | Conv of term * term * term * term (* Conv(t,t1,p,p') is for conv t to t1 by p , p' *)
  | Trans of term * term
  | Unfold
  | Eval
  | Refl
  | Substself
  | Pos of pd * term
and binding = (string * term * term)
;;

type cmd = 
    Def of pd * string * term * term
  | SetFlag of string
  | UnsetFlag of string
  | EvalCmd of term
  | FixCmd of pd * (binding list)
;;
type prog = cmd list;;

(***********************************************************************)
(* a few utility functions *)

let string_of_pos (p:pd) = "File \""^(snd p)^ "\", line " ^ (string_of_int (fst p));;

let err (s : string) =
  print_string s;
  print_string "\n";
  exit 1;;

let err_pos (p:pd) (s:string) =
  err (string_of_pos p ^ ":\n" ^ s)

let is_pos (t:term) : bool =
  match t with
      Pos(_,_) -> true
    | _ -> false;;

let rec strip_pos (t:term) : term =
  match t with
      Pos(_,t') -> strip_pos t'
    | _ -> t;;

(***********************************************************************)
(* printing abstract syntax *)

let rec app_flatten (t:term) (ts: term list) : term list =
  match t with
      App(t1,t2) -> app_flatten t1 (t2::ts)
    | _ -> t::ts;;

let app_flatten (t:term) : term list = app_flatten t [];;

let rec trans_flatten (t:term) (ts: term list) : term list =
  match t with
      Trans(t1,t2) -> trans_flatten t1 (t2::ts)
    | _ -> t::ts;;

let trans_flatten (t:term) : term list = trans_flatten t [];;

let string_of_binder (b:binder) : string =
  match b with
      Pi -> "!"
    | Lam -> "\\";;

Flags.register "print_hidden" "Print any hidden constructs in the abstract syntax tree, like position information.\n" false;;
Flags.register "suppress_lam_types" "Suppress the types of lambda-bound variables when printing" false;;

let rec string_of_term (t:term) : string =
  match t with
      App(_,_) ->
	string_of_app (app_flatten t)
    | Trans(_,_) ->
	string_of_trans (trans_flatten t)
    | Binder(b,x,s,t1,t2) -> 
	let suppress = (b = Lam && Flags.get "suppress_lam_types") in
	  "("^(string_of_binder b) ^ " " ^ x ^ 
	    (if suppress then "" else ((match s with Cbv -> " : " | Cbn -> " :: ") ^ (string_of_term t1))) ^ 
	    " . " ^ (string_of_term t2)^")"
    | Fix(bs,t) ->
	"fix "^(string_of_bindings bs)^" in "^(string_of_term t)
    | Var(x) -> x
    | Self(x,t) -> "self "^x^". "^(string_of_term t)
    | Star -> "*"
    | Check(t1,t2) -> (string_of_term t1)^" : "^(string_of_term t2)
    | Conv(t1,t2,p1,p2) -> 
	"(conv "^(string_of_term t1)^" to "^(string_of_term t2)^" by "^(string_of_term p1) ^ " , " ^ (string_of_term p2)^")"
    | Arrow(t1,s,t2) -> "("^(string_of_term t1) ^ (match s with Cbv -> " -> " | Cbn -> " => ") ^ (string_of_term t2)  ^")"
    | Unfold -> "unfold"
    | Substself -> "substself"
    | Eval -> "eval"
    | Refl -> "refl"
    | Pos(p,t) -> 
	let b = Flags.get "print_hidden" in
	  (if b then "< "^(string_of_pos p)^" " else "")
	  ^(string_of_term t)
	  ^(if b then ">" else "")
and string_of_app (ts:term list) : string =
  match ts with
      t::ts' ->
	"(" ^ (string_of_term t)^(List.fold_right (fun x s -> " " ^ (string_of_term x) ^ s) ts' ")" )
    | [] -> "<internal error: ill-formed application>"
and string_of_trans (ts:term list) : string =
  match ts with
      t::ts' ->
	"[" ^ (string_of_term t)^(List.fold_right (fun x s -> " ; " ^ (string_of_term x) ^ s) ts' "]" )
    | [] -> "<internal error: ill-formed application>"
and string_of_bindings(bs:binding list) : string =
  match bs with
      b::bs' ->
	(string_of_binding b)^(List.fold_right (fun x s -> ", " ^ (string_of_binding x) ^ s) bs' "" )
    | [] -> "<internal error: ill-formed binding list in a fix-term>"
and string_of_binding(b:binding) : string =
  let (x,t,t') = b in
    x^" : "^(string_of_term t)^" = "^(string_of_term t')
;;

(***********************************************************************)
(* converting from concrete to abstract syntax *)

let conv_colon (c:Subcore_syntax.colon) : strategy =
  match c with
      Subcore_syntax.Colon(_,_) -> Cbv
    | Subcore_syntax.Dcolon(_,_) -> Cbn;;

let rec conv_oterm (t:Subcore_syntax.oterm) : term =
  match t with
    | Subcore_syntax.CbvArrow(p,t1,_,t2) -> Pos(p,Arrow(conv_term t1, Cbv, conv_oterm t2))
    | Subcore_syntax.CbnArrow(p,t1,_,t2) -> Pos(p,Arrow(conv_term t1, Cbn, conv_oterm t2))
    | Subcore_syntax.Pi(p,_,x,c,t1,_,t2) ->
	Pos(p,Binder(Pi,snd x, conv_colon c, conv_term t1, conv_oterm t2))
    | Subcore_syntax.Term(p,t) -> Pos(p,conv_term t)
    | Subcore_syntax.Check(p,t1,_,t2) -> Pos(p,Check(conv_term t1,conv_oterm t2))
    | Subcore_syntax.Lam(p,_,x,c,t1,_,t2) ->
	Pos(p,Binder(Lam,snd x, conv_colon c, conv_oterm t1, conv_oterm t2))
    | Subcore_syntax.Fix(p,_,b,(_,bs),_,t2) ->
	Pos(p,Fix(conv_bindings b bs, conv_oterm t2))
    | Subcore_syntax.Self(p,_,x,_,t) ->
	Pos(p,Self(snd x, conv_oterm t))
and conv_term (t:Subcore_syntax.term) : term =
  match t with
    | Subcore_syntax.App(p,_,hd,(_,ts),_) ->
	let rec left_app hd args = 
	  match args with
	      [] -> hd
	    | a::args -> left_app (App(hd,a)) args
	in
	  Pos(p,left_app (conv_term hd) (List.map conv_term ts))
    | Subcore_syntax.Star(p,_) -> Pos(p,Star)
    | Subcore_syntax.Conv(p,_,t1,_,t2,_,pf1,_,pf2) ->
	Pos(p,Conv(conv_oterm t1, conv_oterm t2, conv_term pf1, conv_term pf2))
    | Subcore_syntax.Parens(p,_,t,_) -> Pos(p,conv_oterm t)
    | Subcore_syntax.Var(p,s) ->
	Pos(p,Var(snd s))
    | Subcore_syntax.Substself(p,_) -> 
	Pos(p,Substself)
    | Subcore_syntax.Unfold(p,_) -> 
	Pos(p,Unfold)
    | Subcore_syntax.Eval(p,_) -> 
	Pos(p,Eval)
    | Subcore_syntax.Refl(p,_) -> 
	Pos(p,Refl)
    | Subcore_syntax.Trans(p,_,t,(_,ts),_) ->
	let rec left_trans hd args = 
	  match args with
	      [] -> hd
	    | a::args -> left_trans (Trans(hd,a)) args
	in
	  Pos(p,left_trans (conv_oterm t) (List.map (fun (_,x) -> conv_oterm x) ts))
and conv_bindings b bs =
  (conv_binding b)::(List.map (fun x -> conv_binding (snd x)) bs)
and conv_binding(b:Subcore_syntax.binding) : binding =
  match b with
      Subcore_syntax.Binding(p,x,_,t,_,t') -> (snd x, conv_oterm t, conv_oterm t')
;;

let conv_cmd (d:Subcore_syntax.cmd) : cmd =
  match d with
      Subcore_syntax.Def(p,_,x,_,t1,_,t2) ->
	Def(p,snd x,conv_oterm t1, conv_oterm t2)
    | Subcore_syntax.SetFlag(p,_,x) ->
	SetFlag(snd x)
    | Subcore_syntax.UnsetFlag(p,_,x) ->
	UnsetFlag(snd x)
    | Subcore_syntax.EvalCmd(p,_,t) ->
	EvalCmd(conv_oterm t)
    | Subcore_syntax.FixCmd(p,_,b,(_,bs)) ->
	FixCmd(p,conv_bindings b bs)
;;

let conv_prog (p : Subcore_syntax.prog) : prog =
  match p with
      Subcore_syntax.Prog(_,(_,ds)) -> List.map conv_cmd ds;;

(***********************************************************************)
(* free variables and renaming *)

let rec add_fvs (m:term trie) (t:term) : unit =
  (* restore the old value for each x in xs after recursively processing t *)
  let nonadd xs t =
    let olds = List.map (fun x -> (x,trie_lookup m x)) xs in
      add_fvs m t;
      List.iter (fun (x,old) -> trie_update m x old) olds
  in
    match t with
	Var(x) -> 
	  trie_insert m x t
      | App(t1,t2) | Arrow(t1,_,t2) ->
	  add_fvs m t1; add_fvs m t2
      | Binder(b,x,_,t1,t2) ->
	  add_fvs m t1;
	  nonadd [x] t2
      | Fix(bs,t) ->
	  nonadd (List.map (fun (x,y,z) -> x) bs) t
      | Self(x,t) ->
	  nonadd [x] t
      | Star -> ()
      | Check(t1,t2) | Trans(t1,t2) -> add_fvs m t1; add_fvs m t2
      | Conv(t1,t2,p1,p2) ->
	  add_fvs m t1;
	  add_fvs m t2;
	  add_fvs m p1;
	  add_fvs m p2;
      | Unfold | Eval | Refl | Substself -> ()
      | Pos(_,t) -> add_fvs m t
;;

let rec rename_away (x:string) (m:'a trie) : string =
  if trie_contains m x then
    rename_away (x^"\'") m
  else
    x;;

let rename_away_term (x:string) (t:term) : string =
  let m = trie_new() in
    add_fvs m t;
    rename_away x m;;   

(***********************************************************************)
(* capture-avoiding substitution *)

Flags.register "debug_subst" "Print recursive debugging info for subst." false;;

(* substitute t for x in t', avoiding variable capture *)
let subst (t:term) (x:string) (t':term) : term = 
  let m = trie_new() in

    add_fvs m t;
    add_fvs m t';

    trie_insert m x t;

    let rec subst (t':term) : term = 
      let rename_away_and_subst x t =
	let x' = rename_away x m in
	let old = trie_lookup m x in
	  trie_insert m x (Var(x'));
	  let t' = subst t in
	    trie_update m x old;
	    (x',t')
      in
      let dbg = Flags.get "debug_subst" && not (is_pos t') in
	
	if dbg then
	  (print_string "(subst ";
	   print_string (string_of_term t);
	   print_string " for ";
	   print_string x;
	   print_string " in ";
	   print_string (string_of_term t');
	   print_string "\n";
	   flush stdout);
	
	let ret = 
	  match t' with
	      App(t1,t2) -> App(subst t1, subst t2)
	    | Arrow(t1,s,t2) -> Arrow(subst t1, s, subst t2)
	    | Check(t1,t2) -> Check(subst t1, subst t2)
	    | Trans(t1,t2) -> Trans(subst t1, subst t2)
	    | Star -> Star
	    | Binder(b,x,s,t1,t2) ->
		let t1' = subst t1 in
		let (x',t2') = rename_away_and_subst x t2 in
		  Binder(b,x',s,t1',t2')
	    | Fix(bs,t) ->
		(* return a list of pairs of the vars in xs with their old values (from m) *)
		let rec rename_away_list xs =
		  match xs with
		      [] -> []
		    | x::xs' -> 
			let x' = rename_away x m in
			let old = trie_lookup m x in
			  trie_insert m x (Var(x'));
			  (x,old)::(rename_away_list xs')
		in
		let olds = rename_away_list (List.map (fun(x,y,z) -> x) bs) in
		let bs' = List.map (fun(x,ta,tb) -> (x,subst ta, subst tb)) bs in
		let t' = subst t in
		  List.iter (fun (x,old) -> trie_update m x old) olds;
		  Fix(bs',t')
	    | Var(x) ->
		(match trie_lookup m x with
		     None -> t'
		   | Some(t'') -> t'')
	    | Self(x,t) ->
		let (x',t') = rename_away_and_subst x t in
		  Self(x',t')
	    | Conv(t1,t2,p1,p2) -> Conv(subst t1, subst t2, subst p1, subst p2)
	    | Unfold | Eval | Refl | Substself -> t'
	    | Pos(p,t) -> Pos(p,subst t) in
	  if dbg then
	    (print_string ") subst returns ";
	     print_string (string_of_term ret);
	     print_string "\n";
	     flush stdout);
	  ret
    in
      subst t';;

(***********************************************************************)
(* testing types for equality, and substitution *)

(* map names of variables to (T,b,ot):

   -- T is the type of the variable
   -- b tells whether or not that variable can be treated as a value
   -- ot optionally tells what that variable is defined to equal *)
type ctxt = (term * bool * term option) trie;;

Flags.register "debug_context" "Dump the typing context while type checking." false;;

let dump_ctxt (os:string -> unit) (g:ctxt) : unit =
  os "The typing context is:(\n";
  trie_iter (fun x (t,b,ot) ->
	       os x;
	       os " ::";
	       if b then
		 os "val "
	       else
		 os " ";
	       os (string_of_term t);
	       (match ot with
		    None -> ()
		  | Some(t') -> 
		      os " := ";
		      os (string_of_term t'));
	       os "\n") g;
  os ")\n"
;;
			
(* drop top-level Pos and Conv *)
let rec drop_top_conv (t:term) : term =
  match t with
      Pos(_,t') -> drop_top_conv t'
    | Conv(t,t',p1,p2) -> drop_top_conv t
    | _ -> t;;

let is_val (g:ctxt) (t:term) : bool =
  match (drop_top_conv t) with
      Binder(_,_,_,_,_) -> true
    | Star -> true
    | Self(_,_) -> true
    | Var(s) ->
	(match trie_lookup g s with
	     None -> false
	   | Some(t,b,ot) -> b)
    | _ -> false;;

let add_bindings (g:ctxt) (bs:binding list) : unit =
  List.iter (fun(x,ta,tb) -> trie_insert g x (ta,(is_val g tb),Some(tb))) bs;;

Flags.register "debug_eqterm" "Print debugging information recursively from eqterm." false;;
Flags.register "suppress_eqterm_stack" "Do not print the eqterm stack in type error messages." false;;

let eqterm_stack = Stack.create();;

let rec string_of_eqterm_stack() : string =
  if Stack.is_empty eqterm_stack then
    "<empty>"
  else
    let (t1,t2) = Stack.pop eqterm_stack in
      "   "^(string_of_term t1)^"\n   "^(string_of_term t2)^"\n\n"^
	(string_of_eqterm_stack());;

let string_of_eqterm_stack() : string =
  if Flags.get "suppress_eqterm_stack" then
    "<suppressed>"
  else
    string_of_eqterm_stack();;

let rec eqterm (r:string trie) (t1:term) (t2:term) : bool =
  (* update g to map x to y, check t1a = t2a, then restore r *)
  let identify_names_and_check x y t1a t2a =
    let oldbnd = trie_lookup r x in
      (* map x to y while comparing the bodies *)
      trie_insert r x y;
      let ret = eqterm r t1a t2a in
	trie_update r x oldbnd;
	ret
  in
  let dbg = Flags.get "debug_eqterm" in
    if dbg then
      (print_string "(eqterm ";
       print_string (string_of_term t1);
       print_string " ";
       print_string (string_of_term t2);
       print_string "\n";
       flush stdout);
    
    Stack.push (t1,t2) eqterm_stack;

    let ret = 
      match strip_pos t1, strip_pos t2 with
	  Var(x), Var(y) -> 
	    let lookup v =
	      match trie_lookup r v with
		None -> v
	      | Some(v') -> v'
	    in
	    let x' = lookup x in
	    let y' = lookup y in
	      x' = y'
	| Binder(b1,x,s1,t1a,t1b), Binder(b2,y,s2,t2a,t2b) ->
	    if b1 = b2 && s1 = s2 && eqterm r t1a t2a then
	      identify_names_and_check x y t1b t2b
	    else
	      false
	| Arrow(t1a,s1,t1b) , Binder(b,y,s2,t2a, t2b) | Binder(b,y,s2,t2a, t2b), Arrow(t1a,s1,t1b) ->
	    if s1 = s2 && eqterm r t1a t2a then
	      (* choose a fresh name for y away from the free variables of t1b,
		 just in case t1b contains y free.  Then check if t1b equals the renamed version of t2b. *)
	      let y' = rename_away_term y t1b in
		identify_names_and_check y y' t1b t2b
	    else
	      false
	| App(t1a,t1b), App(t2a,t2b) ->
	    eqterm r t1a t2a && eqterm r t1b t2b
	| Arrow(t1a,s1,t1b), Arrow(t2a,s2,t2b) ->
	    s1 = s2 && eqterm r t1a t2a && eqterm r t1b t2b
	| Star, Star -> true
	| Self(x,t1a), Self(y,t2a) ->
	    identify_names_and_check x y t1a t2a
	| Conv(t1a,t1b,pf1a,pf1b), t2' | t2', Conv(t1a,t1b,pf1a,pf1b) ->
	    (* we disregard conv-constructs when comparing for equality *)
	    eqterm r t1a t2'
	| _,_ -> 
	    false
    in
      if dbg then
	(print_string ") eqterm returns ";
	 print_string (if ret then "true\n" else "false\n");
	 flush stdout);
      (* pop the stack iff we are returning true (leaving it in place if we are returning false) *)
      if ret then
	(let _ = Stack.pop eqterm_stack in
	  ());
      ret
;;

(***********************************************************************)
(* evaluator *)

Flags.register "debug_eval" "Print debugging information recursively from eval" false;;

(* if unf is true, we will unfold variables we encounter automatically *)
let rec eval (g:ctxt) (unf:bool) (t:term) : term =
  let dbg = Flags.get "debug_eval" in
    if dbg then
      (print_string "(eval ";
       print_string (string_of_term t);
       print_string "\n");
    let t = drop_top_conv t in
    let ret = 
      match t with
	  App(t1,t2) ->
	    let e1 = eval g unf t1 in
	      (match drop_top_conv e1 with
		   Binder(Lam,x,s,ta,tb) ->
		     (match s with
			  Cbv ->
			    let e2 = eval g unf t2 in
			      if is_val g e2 then
				eval g unf (subst e2 x tb)
			      else
				(if dbg then
				   (print_string "is_val returns false for ";
				    print_string (string_of_term e2);
				    print_string "\n");
				 App(e1,e2))
			| Cbn ->
			    eval g unf (subst t2 x tb))
		 | _ -> App(e1,t2))
	| Var(x) -> 
	    if unf then
	       (match trie_lookup g x with
		    Some(_,_,Some(v)) -> eval g unf v
		  | _ -> t)
	    else
	      t
	| _ -> t
    in
      if dbg then 
	(print_string ") eval returns ";
	 print_string (string_of_term ret);
	 print_string "\n");
      ret
;;

(***********************************************************************)
(* type checker *)

Flags.register "debug_tpof" "Dump information recursively while type checking." false;;
Flags.register "debug_morph" "Dump information recursively from morph." false;;

let rec tpof (g:ctxt) (p:pd) (t:term) : term =
  let bind_and_tpof (x:string) (t1:term) (s:strategy) (t2:term) : term =
    let old = trie_lookup g x in
      trie_insert g x (t1,(match s with Cbv -> true | Cbn -> false),None);
      let c2 = tpof g p t2 in
	trie_update g x old;
	c2
  in
  let dbg = (Flags.get "debug_tpof" || Flags.get "debug_context") && not (is_pos t) in

    if dbg then
      (print_string "(tpof ";
       print_string (string_of_term t);
       if Flags.get "debug_context" then
	 (print_string " with context:\n";
	  dump_ctxt print_string g);
       print_string "\n";
       flush stdout);

    let ret =
      match t with
	  Star -> Star
	| Var(x) -> 
	    (match trie_lookup g x with
		 None -> 
		   err_pos p ("No declaration for variable "^x^" is currently in scope.\n")
	       | Some(t1,_,_) -> t1)
	| App(t1,t2) ->
	    let c1 = tpof g p t1 in
	    let c2 = tpof g p t2 in
	    let report_mismatch c1a =
	      err_pos p ("An argument in an application does not have the expected type.\n\n"^
			   "1. the argument: "^(string_of_term t2)^
			   "\n2. its type: "^(string_of_term c2)^
			   "\n3. the expected type: "^(string_of_term c1a)^
			   "\n4. the eqterm stack:\n"^(string_of_eqterm_stack()))
	    in
	      (match (strip_pos c1) with
		   Binder(Pi,x,s,c1a,c1b) -> 
		     if eqterm (trie_new()) c1a c2 then
		       (match s with
			    Cbv ->
			      if is_val g t2 then
				subst t2 x c1b
			      else
				App(Binder(Lam,x,Cbv,c1a,c1b),t2)
			  | Cbn -> 
			      subst t2 x c1b)
		     else
		       report_mismatch c1a
		 | Arrow(c1a,s,c1b) ->
		     if eqterm (trie_new()) c1a c2 then
		       c1b
		     else
		       report_mismatch c1a
		 | _ -> 
		     err_pos p ("The functional part of an application has a type which is not a Pi type.\n\n"^
				  "1. the functional part: "^(string_of_term t1)^
				  "\n2. its type: "^(string_of_term c1)))
	| Binder(Lam,x,s,t1,t2) ->
	    let c1 = tpof g p t1 in
	      (match strip_pos c1 with
		   Star -> ()
		 | _ -> 
		     err_pos p ("The classifier of the domain type of a lambda abstraction is not *.\n\n"^
				  "1. the domain type: "^(string_of_term t1)^
				  "\n2. its classifier: "^(string_of_term c1)));
	      Binder(Pi,x,s,t1,bind_and_tpof x t1 s t2)
	| Binder(Pi,x,s,t1,t2) ->
	    let err_if_not_star s t c = 
	      match strip_pos c with
		  Star -> ()
		| _ -> 
		    err_pos p ("The classifier of the "^s^" of a lambda abstraction is not *.\n\n"^
				 "1. the "^s^": "^(string_of_term t)^
				 "\n2. its classifier: "^(string_of_term c))
	    in
	    let c1 = tpof g p t1 in
	      err_if_not_star "domain" t1 c1;
	      let c2 = bind_and_tpof x t1 s t2 in
		err_if_not_star "range" t2 c2;
		Star 
	| Check(t1,t2) ->
	    let c1 = tpof g p t1 in
	      if eqterm (trie_new()) c1 t2 then
		t2
	      else
		err_pos p ("The computed and declared classifiers in a check-term do not match.\n\n"^
			     "1. the computed classifier: "^(string_of_term c1)^
			     "\n2. the declared classifier: "^(string_of_term t2)^
			     "\n3. the eqterm stack:\n"^(string_of_eqterm_stack()))
	| Fix(bs,t1) ->
	    let olds = List.map (fun (x,_,_) -> (x,trie_lookup g x)) bs in
	    let restore() =
	      List.iter (fun (x,old) -> trie_update g x old) olds in

	    let rec check_tps bs =
	      match bs with 
		  [] -> restore() (* we will re-add the bindings in later step with their defining terms *)
		| (x,ta,tb)::bs' ->
		    let ca = tpof g p ta in
		      
		      (* check that ta is indeed a type *)
		      (match strip_pos ca with
			   Star -> ()
			 | _ -> 
			     err_pos p ("The classifier of a recursively defined symbol is not a type.\n\n"^
					  "1. the recursively defined symbol: "^x^
					  "\n2. its classifier: "^(string_of_term ta)^
					  "\n3. the classifier of its classifier (should be *): "^(string_of_term ca)));
		      trie_insert g x (ta,(is_val g tb),None);
		      check_tps bs'
	    in

	      (* 0. check the types of the definitions, restoring the context when done *)
	      check_tps bs;

	      (* 1. now add definitions for all the bindings at once *)
	      add_bindings g bs;

	      (* 2. then check each defining term *)
	      List.iter 
		(fun(x,ta,tb) ->
		   (* check that tb has type ta (in the context with all the bindings added) *)
		   if dbg then
		     print_string ("(tpof fix: checking defining term for "^x^"\n");
		   let cb = tpof g p tb in
		     if not (eqterm (trie_new()) ta cb) then
		       err_pos p ("The classifier computed for a defining term does not match the declared classifier.\n\n"^
				    "1. the defined symbol: "^x^
				    "\n2. the classifier computed for "^x^"'s defining term: "^(string_of_term cb)^
				    "\n3. the declared classifier: "^(string_of_term ta)^
				    "\n4. the eqterm stack:\n"^(string_of_eqterm_stack()));
		     if dbg then
		       print_string (") tpof fix done checking defining term for "^x^"\n"))
		bs;

	      (* 3. check the continuation part of the fix-term in the extended context *)
	      let c1 = tpof g p t1 in
		
	      (* 4. check that the classifier of the continuation part does not contain any binding free *)
	      let m = trie_new() in
		add_fvs m c1;
		List.iter (fun (x,_,_) ->
			     if trie_contains m x then
			       err_pos p ("The classifier computed for the continuation part of a fix-term contains a symbol"^
					    " recursively defined by that fix-term.\n\n"^
					    "1. the classifier computed for the continuation part: "^(string_of_term c1)^
					    "\n2. the recursively defined symbol (occurs free in the classifier computed): "^x))
		  bs;
		
		(* 5. now restore the context *)
		restore();
		
		c1
	| Self(x,t') ->
	    bind_and_tpof x t Cbn t'
	| Arrow(t1,s,t2) -> 
	    let c1 = tpof g p t1 in
	    let c2 = tpof g p t2 in
	    let report_error s t c =
	      err_pos p ("The "^s^" of an arrow term does not have classifier *.\n\n"^
			   "1. the "^s^": "^(string_of_term t)^
			   "\n2. its classifier: "^(string_of_term c))
	    in
	      (match strip_pos c1, strip_pos c2 with
		   Star, Star -> Star
		 | Star, _ -> 
		     report_error "range" t2 c2
		 | _, _ -> 
		     report_error "domain" t1 c1)
	| Conv(t1,t2,pf1,pf2) -> 
	    let c1 = tpof g p t1 in

	    let c2 = tpof g p t2 in

	      (match strip_pos c2 with
		  Star -> ()
		| _ -> 
		    err_pos p ("The classifier we are trying to convert to in a conv-term is not a type.\n\n"^
					  "1. the classifier (the to-part of the conv-term): "^(string_of_term t2)^
					  "\n2. its classifier: "^(string_of_term c2)));

	      let e1 = morph g (trie_new()) p (Some(t1)) c1 pf1 in
	      let e2 = morph g (trie_new()) p (Some(t1)) t2 pf2 in
		if (eqterm (trie_new()) e1 e2) then
		  t2
		else
		  err_pos p ("A conv-term changed the type of a term, but not to the desired type.\n"^
			       "\n1. the computed type:  "^(string_of_term c1)^
			       "\n2. the desired type:   "^(string_of_term t2)^
			       "\n3. converted computed: "^(string_of_term e1)^
			       "\n4. converted desired:  "^(string_of_term e2)^
			       "\n\n5. the eqterm stack:\n"^(string_of_eqterm_stack()))
	| Eval | Unfold | Refl | Trans(_,_) | Substself -> 
	    err_pos p ("A proof construct is being used in a term-only part of the expression.\n\n"
		       ^"1. the subterm which is a proof: "^(string_of_term t))
	| Pos(p,t) -> tpof g p t
    in
      if dbg then
	(print_string ") tpof returns ";
	 print_string (string_of_term ret);
	 print_string "\n";
	 flush stdout);
      ret
(* the subject, if present, is the term whose type has been morphed to t.  Otherwise t has been morphed from 
   a subexpression of the type of the subject. *)
and morph (g:ctxt) (r:string trie) (p:pd) (subj:term option) (t:term) (pf:term) : term =
  let dbg = Flags.get "debug_morph" && not (is_pos pf) in
    
    if dbg then
      (print_string "(morph ";
       (match subj with
	    None -> print_string "None" 
	  | Some(s) -> print_string ("Some("^(string_of_term s)^")"));
       print_string " ";
       print_string (string_of_term t);
       print_string " ";
       print_string (string_of_term pf);
       print_string "\n";
       flush stdout);
    let cong_err s =
      err_pos p ("A "^s^"-proof is being used with a term which is not a "^s^"-term.\n\n"^
		   "1. the term being morphed: "^(string_of_term t)^
		   "\n2. the "^s^"-proof: "^(string_of_term pf)) in
    let ret = 
      match pf with
	| Unfold ->
	    let report_err() =
	      err_pos p ("An unfold-proof is being used to morph a term which is not a defined symbol.\n\n"^
			   "1. the term being converted: "^(string_of_term t))
	    in
	      (match strip_pos t with
		   Var(x) ->
		     (match trie_lookup g x with
			  Some(_,_,Some(t')) -> t'
			| _ ->
			    report_err())
		 | _ -> report_err())
	| Eval -> eval g false t
	| Refl -> t
	| Trans(pf1,pf2) -> 
	    morph g r p subj (morph g r p subj t pf1) pf2
	| Arrow(pf1,s,pf2) ->
	    let y = rename_away_term "q" (App(pf2,t)) in
	      morph g r p subj t (Binder(Pi,y,s,pf1,pf2))
	| App(pf1,pf2) ->
	    (match strip_pos t with
		 App(t1,t2) ->
		   App(morph g r p None t1 pf1, morph g r p None t2 pf2)
	       | _ -> cong_err "application")
		   
	| Binder(b,x,s1,pf1,pf2) ->
	    (match strip_pos t with
		 Binder(b',x',s2,t1,t2) ->
		   if b <> b' || s1 <> s2 then
		     cong_err "Pi"
		   else
		     
		     (* we will map x to x' *)

		     let t1' = morph g r p None t1 pf1 in
		     let old = trie_lookup r x in
		     let old2 = trie_lookup g x' in
		       trie_insert r x x';
		       (* we need to record the fact that x' is a value *)
		       trie_insert g x' (t1,(match s1 with Cbv -> true | Cbn -> false) ,None);

		       (* break down the subject if it is a lambda and we are morphing with a Pi-proof *)
		       let (o,subj') = 
			 if b = Lam then
			   (None,subj)
			 else
			   match subj with
			       None -> (None,None)
			     | Some(s) ->
				 match strip_pos s with
				     Binder(Lam,x'',s3,_,q2) ->
				       if s1 <> s3 then
					 (err_pos p ("A Pi-proof is being used to morph a lambda-term, but the strategies (Cbv vs. Cbn)"^
						     "do not match.\n\n"^
						     "1. the term being morphed: "^(string_of_term t)^
						     "\n2. the Pi-proof: "^(string_of_term pf)));
				       let old1 = trie_lookup r x'' in
					 trie_insert r x'' x';
					 (Some(x'',old1),Some(q2))
				   | _ -> (None,None)
		       in
			 
			 (* now proceed recursively *)
		       let t2' = morph g r p subj' t2 pf2 in
			 trie_update r x old;
			 trie_update g x' old2;
			 
			 (* restore the variable lambda-bound by the subject, if the subject is a lambda *)
			 (match o with
			      None -> ()
			    | Some(x'',old1) -> trie_update r x'' old1);

			 Binder(b,x',s1,t1',t2')
	       | Arrow(t1,s,t2) ->
		   let y = rename_away_term "q" (App(pf,t2)) in
		     morph g r p subj (Binder(Pi,y,s,t1,t2)) pf 
	       | _ -> cong_err "Pi")
	| Var(x) ->
	    let report_err() = 
	      err_pos p ("A variable-proof is being used with a term which is not the same variable.\n\n"^
			   "1. the proof: "^x^
			   "\n2. the term: "^(string_of_term t)) in
	      if eqterm r (Var(x)) t then
		t
	      else
		report_err()
	| Substself ->
	    (match subj with
		None ->
		  err_pos p ("A substself-proof is operating on a subterm of the morphed type of the subject.\n\n"^
			       "1. the subterm: "^(string_of_term t))
	      | Some(s) ->
		  (match strip_pos t with
		      Self(x,t1) ->
			subst s x t1
		    | _ ->
			err_pos p ("A substself-proof is being used with a morphed type which is not a self-type.\n\n"^
				     "1. the morphed type: "^(string_of_term t))))
	| Pos(p',pf') -> morph g r p' subj t pf'
	| _ -> 
	    err_pos p ("Unimplemented proof construct: "^(string_of_term pf))
    in
      if dbg then
	(print_string ") morph returns ";
	 print_string (string_of_term ret);
	 print_string "\n";
	 flush stdout);
      ret
;;
	  
Flags.register "print_commands" "Print back commands after they are processed." false;;

let string_of_cmd (c:cmd) : string =
  (match c with
       SetFlag(s) -> "Set "^s
     | UnsetFlag(s) -> "Unset "^s
     | Def(_,x,t1,t2) -> ("Define "^x^" : "^(string_of_term t1)^" = "^(string_of_term t2))
     | EvalCmd(t) -> "Eval "^(string_of_term t)
     | FixCmd(_,bs) -> "Fix "^(string_of_bindings bs)
  )^"\n"

;;

let rec proc_cmd (g:ctxt) (c:cmd) : unit =
  (match c with
      SetFlag(s) -> Flags.set s true
    | UnsetFlag(s) -> Flags.set s false
    | Def(pos,x,t1,t2) ->
	let c2 = tpof g pos t2 in
	  if eqterm (trie_new()) t1 c2 then
	    trie_insert g x (t1,(is_val g t2),Some(t2))
	  else
	    err (string_of_pos pos ^ ": in a top-level definition, the declared type does not match the computed type.\n\n"^
		   "1. the defined symbol: "^x^
		   "\n2. the declared type: "^(string_of_term t1)^
		   "\n3. the computed type: "^(string_of_term c2)^
		   "\n4. the eqterm stack:\n"^(string_of_eqterm_stack()))
    | EvalCmd(t) ->
	let e = eval g true t in
	  print_string (string_of_term t);
	  print_string " evals to ";
	  print_string (string_of_term e);
	  print_string "\n"
    | FixCmd(p,bs) ->
	let fixterm = Fix(bs,Star) in
	let _ = tpof g p fixterm in
	  add_bindings g bs
  );
  if Flags.get "print_commands" then
    print_string (string_of_cmd c);
;;

let proc_prog(g:ctxt) (p:prog) : unit =
  List.iter (proc_cmd g) p;;

(***********************************************************************)

if Array.length Sys.argv <> 2 then
  err "Run with the name of one .sub file to process.";;

let filename : string = Sys.argv.(1)
let infile = (open_in filename);;

let parsed =
  let lexbuf = Lexing.from_channel infile 
  in Subcore_parse.main Subcore_lex.token lexbuf 
in
  
  match parsed with
      None -> ()
    | Some(x) ->
	let p = conv_prog x in
	let g = trie_new() in
	  proc_prog g p
;;

close_in infile;;
