open External

let (-->) ty_params ty_body = TyFun (ty_params, ty_body)
let tInt = TyCons ("int", [])
let tBool = TyCons ("bool", [])
let tList ty = TyCons ("list", [ty])
let tV a = TyVar a

(* TODO: we want two forms for "infix" variables: 
   one that is the infix form and 
   one that can be used as generic term 
 *)
let sml_std_lib =
  [(* (";",    [tV "b"; tV "a"] --> (tV "a")); *)
   ("0",      tInt);
   ("1",      tInt);
   ("2",      tInt);
   ("(fn (x, y) => x + y)",    [tInt; tInt] --> tInt);
   ("(fn (x, y) => x - y)",    [tInt; tInt] --> tInt);
(*
   ("+",    [tInt; tInt] --> tInt);
   ("-",    [tInt; tInt] --> tInt);
 *)
   ("[]",     tList (tV "a"));
   ("(fn (x, y) => x :: y)",    [tV "a"; tList (tV "a")] --> tList (tV "a"));
(*
   ("::",    [tV "a"; tList (tV "a")] --> tList (tV "a"));
 *)
   ("List.hd",                     [tList (tV "a")] --> tV "a");
   ("List.tl",                     [tList (tV "a")] --> tList (tV "a"));
   ("List.take",                   [tList (tV "a"); tInt] --> tList (tV "a"));
   ("List.nth",                    [tList (tV "a"); tInt] --> tV "a");
   ("List.length",                 [tList (tV "a")] --> tInt);
   ("(fn (x, y) => x @ y)",        [tList (tV "a"); tList (tV "a")] --> tList (tV "a"));
   ("List.filter",                 [[tV "a"] --> tBool] --> ([tList (tV "a")] --> tList (tV "a")));
   ("List.map",                    [[tV "a"] --> tV "b"] --> ([tList (tV "a")] --> tList (tV "b")));
   ("List.foldr",                  [[tV "b"; tV "a"] --> tV "a"] --> ([tV "a"] --> ([tList (tV "b")] --> tV "a")));
   ("(fn (x, y) => x andalso y)",  [tBool; tBool] --> tBool);
   ("(fn (x, y) => x orelse y)",   [tBool; tBool] --> tBool);
(*
   ("andalso",   [tBool; tBool] --> tBool);
   ("orelse",   [tBool; tBool] --> tBool);
 *)
   ("not",    [tBool] --> tBool);
   ("true",   tBool);
   ("false",  tBool);
   ("(raise Fail \"fail!\")", tV "a");
(*
   ("(fn (x, y) => x = y)", [tV "a"; tV "a"] --> tBool);
   Problem term: 
   ((fn (x, y) => x = y) ((fn (x3 : (int), x4 : ((int) list)) => x2), (fn (x, y) => x :: y)))
 *)
   ("(fn (x : int, y : int) => x = y)", [tInt; tInt] --> tBool);
   ("(fn (x : bool, y : bool) => x = y)", [tBool; tBool] --> tBool);
   ("(fn (x : int list, y : int list) => x = y)", [tList tInt; tList tInt] --> tBool);
(*
   ("=", [tInt; tInt] --> tBool);
   ("=", [tBool; tBool] --> tBool);
   ("=", [tList tInt; tList tInt] --> tBool);
 *)
  ]

let string_of_ty (ty0 : ty) =
  let rec toStr wr ty =
    let wrap s =
      if wr
      then "(" ^ s ^ ")"
      else s in
    match ty with
    | TyVar a -> "'" ^ a
    | TyCons ("list", [ty']) ->
       "(" ^ toStr true ty' ^ ") list"
    | TyCons (n, tys) ->
       (match tys with
        | [] -> n
        | _ ->
           wrap (n ^ " " ^ String.concat " " (List.map (toStr true) tys)))
    | TyFun ([], body_ty) ->
       let param_tys = "unit" in
       let body_ty = (toStr true body_ty) in
       wrap (param_tys ^ " -> " ^ body_ty)
    | TyFun (param_tys, body_ty) ->
       let param_tys = "(" ^ String.concat " * " (List.map (toStr true) param_tys) ^ ")" in
       let body_ty = (toStr true body_ty) in
       wrap (param_tys ^ " -> " ^ body_ty)
    in
  toStr false ty0

(* this should be an attribute on the library, probably *)
let is_infix f =
  match f with
  | "+" | "-"
  | ";"
  | "::" | "@"
  | "="
  | "andalso" | "orelse" -> true
  | _ -> false

let make_infix f = f
(*
  String.sub f 1 (String.length f - 2)
 *)

let rec sml_string e =
  match e with
  | Ref (x, ty) ->
     let x_annot () = 
       let ty = string_of_ty ty in
       "(" ^ x ^ " : " ^ ty ^ ")" in
     (match List.assoc_opt x sml_std_lib with
      | None -> x
      | Some _ ->
         if true (* SS.is_empty (ty_vars ty) *)
         then x
         else x_annot ())
  | Lambda (xs, e_body) ->
     (match xs with
      | [] -> 
         let params = "()" in
         let body = sml_string e_body in
         "(fn " ^ params ^ " => " ^ body ^ ")"
      | _ -> 
         let params = "(" ^ (String.concat ", " (List.map (fun (x, ty) -> x ^ " : (" ^ string_of_ty ty ^ ")") xs)) ^ ")" in
         let body = sml_string e_body in
         "(fn " ^ params ^ " => " ^ body ^ ")")
  | Call (e_f, e_args) ->
    (match e_f, e_args with
     | Ref (f, _), [e1; e2] when is_infix f ->
        let e1 = sml_string e1 in
        let infix_f = make_infix f in
        let e2 = sml_string e2 in 
        "(" ^ e1 ^ " " ^ infix_f  ^ " " ^ e2 ^ ")"
     | _, [] ->
        let e_f = sml_string e_f in
        let args = "()" in
        "(" ^ e_f ^ " " ^ args ^ ")"
     | _, _ ->
        let e_f = sml_string e_f in
        let args = "(" ^ (String.concat ", " (List.map sml_string e_args)) ^ ")" in
        "(" ^ e_f ^ " " ^ args ^ ")")
  | Let ((_, _), _, _) -> raise Util.Unimplemented

let generate_sml size =
  let weights x = 
    match x with
    | "List.nth" | "[]" -> 1. /. 3.
    | "List.hd" | "List.tl" -> 1. /. 4.
    | "(raise Fail \"fail!\")" -> 0. (*1. /. 10. *)
    | _ -> 1. in
  let weighted_std_lib =
    List.map (fun entry -> (weights (fst entry), entry)) sml_std_lib in
  let gen_ty = [tList tInt] --> tList tInt in
  Generate.generate_exp weighted_std_lib size (tV "a") gen_ty
  (* TODO: program stats in debug mode *)

let generate_batch exp_size batch_size =
  Seq.init batch_size
           (fun _ ->
             let p = generate_sml exp_size in
             Debug.run prerr_newline;
             p)

let print_file tests =

  let rec print_lines pre post lines =
    match lines with
    | [] -> ()
    | [l] -> print_string pre; print_endline l
    | l :: lines' ->
       print_string pre;
       print_string l;
       print_endline post;
       print_lines pre post lines' in

  let prelude = [
      "structure Test = struct";
    ] in

  let main = [
      "fun runTests tests = ";
      "   case tests";
      "    of [] => ()";
      "     | test :: tests => (";
      "      ((test () [0, 1, 2, 3]";
      "        handle Empty => [])";
      "        handle Subscript => []);";
      "      runTests tests";
      "     )";
      "";
      "fun main () = runTests testList"
    ] in

  let postlude = [
      "end";
    ] in

  print_lines "" "" prelude;
  print_endline "   val testList = ["; (* : ((int list) -> (int list)) list = [ *)
  let tests = List.map (fun test -> "(fn () => " ^ test ^ ") : unit -> (int list) -> (int list)") tests in
  print_lines "     " "," tests;
  print_endline "   ]";
  print_endline "";
  print_lines "   " "" main;
  print_lines "" "" postlude;
  ()

let n = ref 100
let size = ref 25
let seed = ref (-1)

let speclist =
  [
    ("-n", Arg.Set_int n, "Number of functions to generate");
    ("-size", Arg.Set_int size, "Size of each function");
    ("-seed", Arg.Set_int seed, "Random generator seed");
    ("-debug", Arg.Set Debug.debug_mode, "Enable debug mode");
  ]

(* -O -fno-full-laziness *)
let () =
  Arg.parse speclist (fun _ -> ())
    "gen_sml [-testtype <0>] [-n <100>] [-size <100>] [-seed <-1>]";
  (if !seed < 0
   then Random.self_init ()
   else Random.init !seed);

  let fs = Seq.map sml_string (generate_batch !size !n) in
  print_file (List.of_seq fs)
