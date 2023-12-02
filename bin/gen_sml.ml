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
let n (str, ty) = (str, (ty, None))

let infix (str, ty) = ("op" ^ str, (ty, Some (fun arg1 arg2 -> arg1 ^ " " ^ str ^ " " ^ arg2)))

let eq str_ty ty = 
  ("(fn (x : " ^ str_ty ^ ", y : " ^ str_ty ^ ") => x = y)", 
   ([ty; ty] --> tBool,
    Some (fun arg1 arg2 -> "((" ^ arg1 ^ ") : " ^ str_ty ^ ")  = ((" ^ arg2 ^ ") : " ^ str_ty ^ ")")))

let sml_std_lib =
  [(* (";",    [tV "b"; tV "a"] --> (tV "a")); *)
    n("0",      tInt);
    n("1",      tInt);
    n("2",      tInt);
    infix("+",  [tInt; tInt] --> tInt);
    infix("-",  [tInt; tInt] --> tInt);

    n("[]",           tList (tV "a"));
    infix("::",       [tV "a"; tList (tV "a")] --> tList (tV "a"));
    n("List.hd",      [tList (tV "a")] --> tV "a");
    n("List.tl",      [tList (tV "a")] --> tList (tV "a"));
    n("List.take",    [tList (tV "a"); tInt] --> tList (tV "a"));
    n("List.nth",     [tList (tV "a"); tInt] --> tV "a");
    n("List.length",  [tList (tV "a")] --> tInt);
    infix("@",        [tList (tV "a"); tList (tV "a")] --> tList (tV "a"));
    n("List.filter",  [[tV "a"] --> tBool] --> ([tList (tV "a")] --> tList (tV "a")));
    n("List.map",     [[tV "a"] --> tV "b"] --> ([tList (tV "a")] --> tList (tV "b")));
    n("List.foldr",   [[tV "b"; tV "a"] --> tV "a"] --> ([tV "a"] --> ([tList (tV "b")] --> tV "a")));

    n("true",   tBool);
    n("false",  tBool);
    n("not",    [tBool] --> tBool);
    ("(fn (x, y) => x andalso y)", 
     ([tBool; tBool] --> tBool,
      Some (fun arg1 arg2 -> arg1 ^ " andalso " ^ arg2)));
    ("(fn (x, y) => x orelse y)", 
     ([tBool; tBool] --> tBool,
      Some (fun arg1 arg2 -> arg1 ^ " orelse " ^ arg2)));

    n("(raise Fail \"fail!\")", tV "a");
    (*
      ("(fn (x, y) => x = y)", [tV "a"; tV "a"] --> tBool);
      Problem term: 
      ((fn (x, y) => x = y) ((fn (x3 : (int), x4 : ((int) list)) => x2), (fn (x, y) => x :: y)))
     *)
    eq "int" tInt;
    eq "bool" tBool;
    eq "int list" (tList tInt);
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
       wrap (toStr true ty' ^ " list")
    | TyCons (n, tys) ->
       (match tys with
        | [] -> n
        | _ ->
           raise Util.Unimplemented
(*
             wrap (String.concat " " (List.map (toStr true) tys) ^ " " ^ n)
 *)
       )
    | TyFun ([], body_ty) ->
       let param_tys = "unit" in
       let body_ty = (toStr true body_ty) in
       wrap (param_tys ^ " -> " ^ body_ty)
    | TyFun ([param_ty], body_ty) ->
       let param_ty = toStr true param_ty in
       let body_ty = toStr true body_ty in
       wrap (param_ty ^ " -> " ^ body_ty)
    | TyFun (param_tys, body_ty) ->
       let param_tys = "(" ^ String.concat " * " (List.map (toStr true) param_tys) ^ ")" in
       let body_ty = (toStr true body_ty) in
       wrap (param_tys ^ " -> " ^ body_ty)
        in
  toStr false ty0

let infixOf f = 
  match f with
  | Ref (f, _) -> 
      (match List.assoc_opt f sml_std_lib with
       | Some (_, opt) -> opt
       | None -> None)
  | _ -> None

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
         let params = "(" ^ (String.concat ", " (List.map (fun (x, ty) -> x ^ " : " ^ string_of_ty ty) xs)) ^ ")" in
         let body = sml_string e_body in
         "(fn " ^ params ^ " => " ^ body ^ ")")
  | Call (e_f, e_args) ->
    (match e_f, e_args, infixOf e_f with
     | Ref (_, _), [e1; e2], Some fn ->
        let e1 = sml_string e1 in
        let e2 = sml_string e2 in 
        let result = fn e1 e2 in
        "(" ^ result ^ ")"
     | _, [], _ ->
        let e_f = sml_string e_f in
        let args = "()" in
        "(" ^ e_f ^ " " ^ args ^ ")"
     | _, _, _ ->
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
    List.map (fun (x, (ty, _)) -> (weights x, (x, ty))) sml_std_lib in
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
      (*
      "(* SML Basis *)";
      "";
      "datatype order = LESS | EQUAL | GREATER";
      "";
      "structure Int =";
      "  struct";
      "";
      "    fun compare (s1 : int, s2) =";
      "	  if (s1 < s2) then LESS";
      "	  else if (s2 < s1) then GREATER";
      "	  else EQUAL";
      "";
      "  end";
      "";
      "structure String =";
      "  struct";
      "";
      "    fun compare (s1 : string, s2) =";
      "	  if (s1 < s2) then LESS";
      "	  else if (s2 < s1) then GREATER";
      "	  else EQUAL";
      "";
      "  end";
      "";
      "structure List =";
      "  struct";
      "";
      "    exception Empty";
      "    exception Subscript";
      "";
      "    fun hd [] = raise Empty";
      "      | hd (x::_) = x";
      "";
      "    fun tl [] = raise Empty";
      "      | tl (_::xs) = xs";
      "";
      "    fun nth ([], _) = raise Subscript";
      "      | nth (x::_, 0) = x";
      "      | nth (_::r, n) = nth(r, n-1)";
      "";
      "    (* TODO: inefficient for negative indices *)";
      "    fun take (_, 0) = []";
      "      | take ([], _) = raise Subscript";
      "      | take (x::xs, i) = x :: (take (xs, i-1))";
      "";
      "    fun length xs = let";
      "          fun lp (xs, n) = (case xs of [] => n | (_::r) => lp(r, n+1))";
      "          in";
      "            lp (xs, 0)";
      "          end";
      "";
      "    fun revAppend (xs, ys) = (case xs of [] => ys | x::xr => revAppend (xr, x::ys))";
      "";
      "    fun rev xs = revAppend (xs, [])";
      "";
      "    fun filter f xs = let";
      "          fun lp (xs, ys) = (case xs";
      "                 of [] => rev ys";
      "                  | x::xr => if f x then lp (xr, x::ys) else lp (xr, ys)";
      "                (* end case *))";
      "          in";
      "            lp (xs, [])";
      "          end";
      "";
      "    fun append (xs, ys) = (case (xs, ys)";
      "           of ([], _) => ys";
      "            | (_, []) => xs";
      "            | _ => revAppend (rev xs, ys)";
      "          (* end case *))";
      "";
      "    fun map f xs = let";
      "          fun mapf xs = (case xs of [] => [] | (x::xr) => f x :: mapf xr)";
      "          in";
      "            mapf xs";
      "          end";
      "";
      "    fun foldl f init xs = let";
      "          fun foldf ([], acc) = acc";
      "            | foldf (x::xr, acc) = foldf (xr, f(x, acc))";
      "          in";
      "            foldf (xs, init)";
      "          end";
      "";
      "    fun foldr f init xs = let";
      "          fun foldf ([], acc) = acc";
      "            | foldf (x::xr, acc) = f (x, foldf (xr, acc))";
      "          in";
      "            foldf (xs, init)";
      "          end";
      "";
      "    fun exists f xs = let";
      "          fun existsf xs = (case xs";
      "                 of [] => false";
      "                  | (x::xr) => f x orelse existsf xr";
      "                (* end case *))";
      "          in";
      "            existsf xs";
      "          end";
      "";
      "    fun collate cmp ([], []) = EQUAL";
      "      | collate cmp ([], _) = LESS";
      "      | collate cmp (_, []) = GREATER";
      "      | collate cmp (x::xs, y::ys) = (case cmp (x, y)";
      "	   of EQUAL => collate cmp (xs, ys)";
      "	    | order => order";
      "	  (* end case *))";
      "";
      "  end";
      "";
      "val op @ = List.append";
      "";
      "fun not false = true";
      "  | not true = false";
      "";
      *)
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
