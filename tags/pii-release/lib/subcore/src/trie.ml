open Char;;

type 'a trieh = Tnone 
             | Tnext of 'a option * 'a trieh array

let array_len = 128;;
let mk_triehvec a = (Array.make array_len a);;

let rec trieh_update (t:'a trieh) (s:char list) (a:'a option) = 
  match t with 
    Tnone -> (trieh_update (Tnext(None,(mk_triehvec Tnone))) s a)
  | Tnext(o,v) ->
       match s with
         [] -> Tnext(a,v)
       | c::s' -> 
           let cc = (code c) in
           Array.set v cc (trieh_update (Array.get v cc) s' a);
           Tnext(o,v)

let rec trieh_lookup t s = 
   match t with
     Tnone -> None
   | Tnext(o,v) -> 
       match s with
         [] -> o
       | c::s' -> trieh_lookup (Array.get v (code c)) s'



let rec charlist_of_string s i =
  if (i = String.length s) then
    []
  else
    (s.[i])::(charlist_of_string s (i+1));;

let charlist_of_string s = charlist_of_string s 0;;

let rec string_of_charlist l i iend s =
  if i = iend then s
  else
    (String.set s i (List.hd l);
     string_of_charlist (List.tl l) (i+1) iend s);;

let string_of_charlist l = 
  let len = (List.length l) in
    string_of_charlist l 0 len (String.create len);;

let rec trieh_strings (t : 'a trieh) (sofar : char list) (strs : string list) : string list =
  match t with 
     Tnone -> strs
   | Tnext(o,v) -> match o with
                   None -> trieh_strings_elems v 0 sofar strs
                 | Some(trm) -> trieh_strings_elems v 0 sofar ((string_of_charlist (List.rev sofar))::strs)
and trieh_strings_elems (arr : 'a trieh array) (next_index:int) (sofar : char list) (strs : string list) : string list =
  if (next_index = array_len) then
    strs
  else
    let elem_strings = trieh_strings arr.(next_index) ((chr next_index)::sofar) strs in
      trieh_strings_elems arr (next_index+1) sofar elem_strings;;


type 'a trie = 'a trieh ref;;

let trie_new () = ref Tnone;;

let trie_insert (t:'a trie) (s:string) (a:'a) : unit = t := trieh_update !t (charlist_of_string s) (Some(a));;

let trie_remove (t:'a trie) (s:string) : unit = t := trieh_update !t (charlist_of_string s) None;;

let trie_lookup (t:'a trie) (s:string) : 'a option = trieh_lookup !t (charlist_of_string s);;

let trie_update (t:'a trie) (s:string) (a:'a option) = t := trieh_update !t (charlist_of_string s) a;;

let trie_contains (t:'a trie) (s:string) : bool =
  match (trie_lookup t s) with
      Some(_) -> true
    | _ -> false;;

let trie_strings (t:'a trie) : string list = trieh_strings !t [] [];;

let trie_iter (f:string -> 'a -> unit) (t:'a trie) : unit =
  List.iter (fun x ->
	       (match (trie_lookup t x) with
		    None -> print_string "[trie internal error, missing string]"; exit 1 (* should never happen *)
		  | Some(d) -> f x d))
    (trie_strings t);;

let trie_print (os:string -> unit) (print_value : 'a -> unit) (t:'a trie) : unit = 
  trie_iter (fun x d -> 
	       os x; 
	       os " -> ";
	       print_value d;
	       os "\n") t;;

let trie_clear (t:'a trie) : unit = (t := Tnone);;

