let (flagtbl : (string, bool) Hashtbl.t) = Hashtbl.create 1024;; (* values of flags *)
let flagdtbl = Hashtbl.create 1024;; (* descriptions *)
let flags = ref ([]:string list);;

(* s is the flag name, d is the description, b is the initial boolean value *)
let register s (d:string) (b:bool) = Hashtbl.add flagtbl s b; Hashtbl.add flagdtbl s d; flags := (s::!flags);;

let get s : bool = 
  if (not (Hashtbl.mem flagtbl s)) then
    raise (Failure ("Unknown flag \""^s^"\""))
  else
    Hashtbl.find flagtbl s
;;

let set s (b:bool) = 
  if (not (Hashtbl.mem flagtbl s)) then
    raise (Failure ("Unknown flag \""^s^"\""))
  else
    Hashtbl.add flagtbl s b
;;

let flags_to_string () =
  List.fold_right (fun f s -> 
		     (f^" : "^(Hashtbl.find flagdtbl f)^" Value is "
		      ^(string_of_bool (Hashtbl.find flagtbl f))
		      ^".\n"^s)) !flags "";;

let flag_descriptions () =
  String.concat "\n"
    (List.map (fun f ->
                 f ^ " : " ^ (Hashtbl.find flagdtbl f)
                 ^ " (Default: "
                 ^ (string_of_bool (Hashtbl.find flagtbl f)) ^ ")")
       !flags);;
