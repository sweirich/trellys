(* auto-generated by gt *)
let usage = "./grammar_name [options] <file> 
    The options are:
       -p      Reprints the contents of <file> to
               <file>pp.txt. Without this option
               the contents are printed to the terminal.
       -a      Prints a text view of <file>'s AST to 
               <file>ast.txt.
       -g      Outputs a Graphviz file named <file>gviz.dot
               that contains a visual representation of <file>'s
               syntax tree.
       -help   prints this
"
let num_args : int = Array.length Sys.argv
let file_name : string = Sys.argv.(num_args - 1)
let ofile (file:string) : (string->unit) = output_string (open_out file);;


let is_flag (arg:string) : bool = 
  let rec is_flag (i:int) : bool = 
	 if i = num_args then false
    else if arg = Sys.argv.(i) then true
	 else is_flag (i + 1)
  in is_flag 0
;;

let () =
  if is_flag "-help" || num_args <= 1 then (print_string usage; exit 1);
  let parsed =
     let lexbuf = Lexing.from_channel (
       if num_args > 1 then (open_in Sys.argv.(num_args - 1)) 
	    else stdin) 
	  in Subcore_parse.main Subcore_lex.token lexbuf 
in

  match parsed with
		None -> ()
	 | Some(x) ->
		if is_flag "-p" then (
		  let os = ofile (file_name^"pp.txt") in
        Subcore_pp.pp os true x;
		  print_string "finished pretty print";
		) else Subcore_pp.pp print_string true x;
      print_string "\n";
		if is_flag "-a" then (
		  let os = ofile (file_name^"ast.txt") in
        Subcore_ppast.ppast os false x;
		  print_string "finished ast\n";
		);

		if is_flag "-g" then (
		  let os = ofile (file_name^"gviz.dot") in
        Subcore_gviz.gviz os false "" x;
		  print_string "finished gviz\n"
		); 

		print_string "done\n"
