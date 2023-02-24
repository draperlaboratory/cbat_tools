(***************************************************************************)
(*                                                                         *)
(*  Copyright (C) 2018/2019 The Charles Stark Draper Laboratory, Inc.      *)
(*                                                                         *)
(*  This file is provided under the license found in the LICENSE file in   *)
(*  the top-level directory of this project.                               *)
(*                                                                         *)
(*  This work is funded in part by ONR/NAWC Contract N6833518C0107.  Its   *)
(*  content does not necessarily reflect the position or policy of the US  *)
(*  Government and no official endorsement should be inferred.             *)
(*                                                                         *)
(***************************************************************************)

open !Core
open Bap.Std

module Expr = Z3.Expr
module Bool = Z3.Boolean
module BV = Z3.BitVector
module Model = Z3.Model
module Solver = Z3.Solver

type z3_expr = Expr.expr

type path = bool Jmp.Map.t

(* A map containing pairs of a register and its value at specific jumps in the program. *)
type reg_map = (z3_expr * z3_expr) list Jmp.Map.t

type goal = { goal_name : string; goal_val : z3_expr }

type refuted_goal = { goal : goal; path : path; reg_map : reg_map }

let eval_model_exn (model : Model.model) (expr : z3_expr) : z3_expr =
  Model.eval model expr true
  |> Option.value_exn
    ?here:None
    ~error:(Error.of_string "eval_model_exn: Error evaluating expression with model.")
    ~message:(Format.sprintf "Unable to evaluate expr %s with current model."
                (Expr.to_string expr))

let get_model_exn (solver : Solver.solver) : Model.model =
  Solver.get_model solver
  |> Option.value_exn
    ?here:None
    ~error:(Error.of_string "get_model_exn: Error getting the model from the Z3 solver.")
    ~message:(Format.sprintf "Unable to get the model from the Z3 solver : %s"
                (Solver.to_string solver))

let goal_to_string ?colorful:(colorful = false) (g : goal) : string =
  let rm_backslash = String.substr_replace_all ~pattern:"\\" ~with_:"" in 
  let lhs = g.goal_name |> rm_backslash in 
  let rhs = (Expr.to_string (Expr.simplify g.goal_val None)) |> rm_backslash in
  if colorful then
    (* lhs is blue, rhs is cyan *)
    Format.sprintf "%s%s%s: %s%s%s%!"
      ("\x1b[1;34m") lhs ("\x1b[0m") ("\x1b[1;36m") rhs ("\x1b[0m")
  else Format.sprintf "%s: %s" lhs rhs


let expr_to_hex (exp : z3_expr) : string =
  let decimal = BV.numeral_to_string exp in
  let size = exp |> Expr.get_sort |> BV.get_size in
  let word = Word.of_string (Printf.sprintf "%s:%du" decimal size) in
  let pp_word ppf =
    Word.pp_generic ~case:`lower ~prefix:`none ~suffix:`none ~format:`hex ppf in
  let word_str = Format.asprintf "%a" pp_word word in
  (* Calculate how many 0s to pad the output with. *)
  let width = if size mod 4 = 0 then size / 4 else size / 4 + 1 in
  let padding = String.make (width - (String.length word_str)) '0' in
  Printf.sprintf "0x%s%s" padding word_str

let format_values (fmt : Format.formatter) (vals : (string * z3_expr) list) : unit =
  let max_str_length =
    vals
    |> List.map ~f:(fun (v, _) -> String.length v)
    |> List.max_elt ~compare:Int.compare
  in
  match max_str_length with
  | None -> ()
  | Some length ->
    List.iter vals
      ~f:(fun (var, value) ->
          let pad_size = length - (String.length var) + 1 in
          let pad = String.make pad_size ' ' in
          Format.fprintf fmt
            "\t%s%s|->  @[%s@]@\n" var pad (expr_to_hex value))

let format_registers (fmt : Format.formatter) (regs : reg_map) (jmp : Jmp.t)
    (var_map : z3_expr Var.Map.t) : unit =
  match Jmp.Map.find regs jmp with
  | None -> ()
  | Some regs ->
    let reg_vals =
      Var.Map.fold var_map ~init:[]
        ~f:(fun ~key ~data pairs ->
            match List.find regs ~f:(fun (r, _) -> Expr.equal data r) with
            | None -> pairs
            | Some (_, value) -> (Var.to_string key, value) :: pairs)
    in
    format_values fmt reg_vals;
    Format.fprintf fmt "\n%!"

let format_path
    (fmt : Format.formatter)
    (p : path)
    (regs : reg_map)
    ~orig:(var_map1, sub1 : z3_expr Var.Map.t * Sub.t)
    ~modif:(var_map2, _ : z3_expr Var.Map.t * Sub.t)
  : unit =
  Format.fprintf fmt "\n\tPath:\n%!";
  let print_path path var_map =
    Jmp.Map.iteri path
      ~f:(fun ~key:jmp ~data:taken ->
          let jmp_str =
            jmp
            |> Jmp.to_string
            |> String.substr_replace_first ~pattern:"\n" ~with_:"" in
          let taken_str = if taken then "(taken)" else "(not taken)" in
          begin
            match Term.get_attr jmp address with
            | None ->
              Format.fprintf fmt "\t%s %s (Address not found)\n%!" jmp_str taken_str
            | Some addr ->
              Format.fprintf fmt "\t%s %s (Address: %s)\n%!"
                jmp_str taken_str (Addr.to_string addr)
          end;
          format_registers fmt regs jmp var_map)
  in
  (* Partition the combined path type into the path in the original binary and
     the path in the modified binary by matching on the jmps found in the subs. *)
  let path_orig, path_mod =
    let jmps1 = Term.enum blk_t sub1 |> Seq.map ~f:(Term.enum jmp_t) |> Seq.concat in
    Jmp.Map.partitioni_tf p ~f:(fun ~key:jmp ~data:_ -> Seq.exists jmps1 ~f:(Jmp.equal jmp))
  in
  (* In the case of a single binary analysis, the path is stored in path_orig. *)
  if Jmp.Map.is_empty path_mod then
    print_path path_orig var_map1
  else begin
    Format.fprintf fmt "\n\tOriginal:\n%!";
    print_path path_orig var_map1;
    Format.fprintf fmt "\n\tModified:\n%!";
    print_path path_mod var_map2
  end

let format_goal (fmt : Format.formatter) (g : goal) (model : Model.model) : unit =
  Format.fprintf fmt "%s:" g.goal_name;
  if Bool.is_eq g.goal_val then
    begin
      let args = Expr.get_args g.goal_val in
      Format.fprintf fmt "\n\tConcrete values: = ";
      List.iter args ~f:(fun arg ->
          let value = eval_model_exn model arg in
          Format.fprintf fmt "%s " (Expr.to_string value));
      Format.fprintf fmt "\n\tZ3 Expression: = ";
      List.iter args ~f:(fun arg ->
          let simplified = Expr.simplify arg None in
          Format.fprintf fmt "%s " (Expr.to_string simplified));
    end
  else
    Format.fprintf fmt "\n\tZ3 Expression: %s"
      (Expr.to_string (Expr.simplify g.goal_val None))

let format_refuted_goal
    (rg : refuted_goal)
    (model : Model.model)
    ~orig:(orig : z3_expr Var.Map.t * Sub.t)
    ~modif:(modif : z3_expr Var.Map.t * Sub.t)
    ~print_path:(print_path : bool)
  : string =
  let fmt = Format.str_formatter in
  format_goal fmt rg.goal model;
  if print_path then format_path fmt rg.path rg.reg_map ~orig ~modif;
  Format.flush_str_formatter ()

let goal_of_refuted_goal (rg : refuted_goal) : goal =
  rg.goal

let mk_goal (name : string) (value : z3_expr) : goal =
  { goal_name = name; goal_val = value }

let get_goal_name (g : goal) : string =
  g.goal_name

let get_goal_val (g : goal) : z3_expr =
  g.goal_val

type t =
  | Goal of goal
  | ITE of Jmp.t * z3_expr * t * t
  | Clause of t list * t list
  | Subst of t * z3_expr list * z3_expr list

(* preen_expr expr will improve the readability
   of expr by getting rid of white space 
   and simplifying the expression. *)
let preen_expr (expr : Expr.expr) : string =
  Expr.simplify expr None
  |> Expr.to_string
  |> String.substr_replace_all ~pattern:"  " ~with_:""

(* delete_empty_constr_hyps const will remove 
   some empty lists in Clause constructs. For example
   Clause([],Clause[Clause([],[x]),y]) becomes 
   Clause([],Clause[x,y]). *)
let rec del_empty_constr_hyps (const : t) : t =
  match const with
  | Clause(hyps,concs) ->
    let fold_list c_list =
      List.fold_right c_list ~init:[]
        ~f:(fun x y ->
            match x with
            | Clause([],xs) ->
              List.append (List.map xs ~f:del_empty_constr_hyps) y
            | _ -> (del_empty_constr_hyps x) :: y) in
    Clause(fold_list hyps, fold_list concs)
  | Goal g -> Goal g
  | ITE (ite, e, c1, c2) ->
    let new_c1 = del_empty_constr_hyps c1 in
    let new_c2 = del_empty_constr_hyps c2 in
    ITE (ite, e, new_c1, new_c2)
  | Subst (c, olds, news) ->
    let new_c = del_empty_constr_hyps c in
    Subst (new_c, olds, news)

(* to_color colorful ch c str ins will print str with insert
   ins and formatter ch. If colorful is true, then this will 
   print in the color c. *)
let to_color (colorful : bool) (ch : Format.formatter) (c : int)
    (str : ('a -> 'b, Format.formatter, unit) Stdlib.format)
    (ins : string) : unit =
  if colorful then Format.fprintf ch "\x1b[1;%dm" c;
  Format.fprintf ch str ins;
  if colorful then Format.fprintf ch "\x1b[0m"

(* print_expr_list expr_list ch converts expr_list into a list of 
   strings of expressions and then prints each one on a new line 
   using the formatter ch *)
let print_expr_list (expr_list : Expr.expr list)
    (ch : Format.formatter) : unit =
  let expr_string_list : string list =
    List.map expr_list ~f:(fun e -> preen_expr e |> String.split_lines)
    |> List.join in
  let rec print_exprs ch exprs =
    match exprs with
    | [] -> ();
    | [e] -> Format.fprintf ch "%s" e
    | e :: es -> Format.fprintf ch "%s@;" e ; print_exprs ch es in 
  Format.fprintf ch "@[<v 2>%a@]" print_exprs expr_string_list

let pp ?colorful:(colorful = false) (_ : unit)
    (fmt : Format.formatter) (t : t) : unit =
  let rec rec_pp ch constr =
    let to_color = to_color colorful ch in
    match constr with
    | Goal g ->
      Format.fprintf ch "%s@;" (goal_to_string ~colorful g)
    | ITE (tid, e, c1, c2) ->
      let color = 35 in (* magenta *)
      to_color color "%s: (if " (tid |> Term.tid |> Tid.to_string);
      Format.fprintf ch "%s" (preen_expr e);
      to_color color " then%s" "";
      Format.fprintf ch "@[@;%a@]" rec_pp c1;
      to_color color " else%s" "";
      Format.fprintf ch "@;%a" rec_pp c2;
      to_color color ")%s" "";
    | Clause (hyps, concs) ->
      (if not (List.is_empty hyps) then 
         let print_hyps =
           List.iter hyps
             ~f:(fun h -> Format.fprintf ch "%a" rec_pp h) in
         print_hyps; 
         let color = 33 in (* yellow *)
         to_color color " => %s" "") ;
      (List.iter concs ~f:(fun c -> Format.fprintf ch "%a" rec_pp c));
    | Subst (c, olds, news) ->
      let color = 32 in (* green *)
      to_color color "(let %s" "";
      Format.fprintf ch "%s" (List.to_string ~f:(preen_expr) olds);
      to_color color " = %s" "";
      print_expr_list news ch;
      to_color color " in%s" "";
      Format.fprintf ch "@;%a" rec_pp c;
      to_color color ")%s" "";
  in
  rec_pp fmt (del_empty_constr_hyps t)

let to_string ?(colorful=false) (constr : t) : string =
  let pp_constr = pp ~colorful:colorful () in 
  Format.asprintf "%a" pp_constr constr 
  |> String.substr_replace_all ~pattern:"\"" ~with_:""
  |> Scanf.unescaped 

let mk_constr (g : goal) : t =
  Goal g

let mk_ite (jmp : Jmp.t) (cond : z3_expr) (c1 : t) (c2 : t) : t =
  ITE (jmp, cond, c1, c2)

let mk_clause (hyps: t list) (concs : t list) : t =
  Clause (hyps, concs)


(* list_stats, std_dev, update_stats and init_stats are used for
   debugging and statistics-gathering for eval_aux *)
type list_stats =
  { mutable sum: int;
    mutable sum_squared: int;
    mutable count: int;
    mutable maximum : int; }

let std_dev stats =
  sqrt ((float stats.sum_squared) /. float stats.count -.
        ((float stats.sum) /. float stats.count) ** 2.)

let update_stats stats olds =
  let list_length = List.length(olds) in
  stats.count <- stats.count + 1;
  stats.sum <- stats.sum + list_length;
  stats.sum_squared <- stats.sum_squared + list_length * list_length;
  stats.maximum <- max stats.maximum list_length

let init_stats = {sum = 0 ; sum_squared = 0 ; count = 0; maximum = 0}

let rec eval_aux ?stats:(stats = init_stats) (constr : t) (olds : z3_expr list)
    (news : z3_expr list) (ctx : Z3.context) : z3_expr =
  update_stats stats olds;
  match constr with
  | Goal { goal_val = v; _ } ->
    Expr.substitute v olds news
  | ITE (_, e, c1, c2) ->
    let e' = Expr.substitute e olds news in
    Bool.mk_ite ctx e' (eval_aux ~stats:stats c1 olds news ctx)
      (eval_aux ~stats:stats c2 olds news ctx)
  | Clause (hyps, concs) ->
    let eval_conjunction conj =
      (* This adds possible tail recursion, avoids And node. *)
      match conj with
      | []  -> Bool.mk_true ctx
      | [x] -> eval_aux ~stats:stats x olds news ctx
      | _   -> Bool.mk_and ctx @@
        List.map conj ~f:(fun c -> eval_aux ~stats:stats c olds news ctx)
    in
    if List.is_empty hyps then
      eval_conjunction concs(* possibly tail recursive? *)
    else
      let concs_expr = eval_conjunction concs in
      let hyps_expr = eval_conjunction hyps in
      Bool.mk_implies ctx hyps_expr concs_expr
  | Subst (c, o, n) ->
    (* The following should be functionally equivalent to 
       [eval_aux ~stats:stats c (olds @ o) (news @ n') ctx] with changes made to achieve 
       better performance. Duplicate keys are pruned from the olds list.

       NOTE : It is assumed as an invariant that the olds list does not contain duplicate 
       keys. Failure to maintain this invariant may result in incorrect behavior.

       Using a Map data structure was tried and it was found that shuffling in and out to 
       lists for Expr.substitute made it slow. Instead, two lists are maintained and 
       pruned of duplicate keys. The most recently used items are put at the front of the
       list to make it fast to find the most commonly used variables.
    *)
    let n' = List.map n ~f:(fun x -> Expr.substitute x olds news) in
    if (List.length n') = 1 (* It appears we generate overwhelmingly size 1 lists *)
    then 
      begin
        let o = List.hd_exn o in
        let n' = List.hd_exn n' in
        (* [removen_exn n l] removes item at position [n] in list [l] *)
        let rec removen_exn n l = 
          match l with 
          | x :: xs ->  if (n = 0) 
            then xs 
            else x :: (removen_exn (n - 1) xs) 
          | [] -> failwith "Improper removen use" in
        let oind = List.findi olds ~f:(fun _ e -> Expr.equal o e) in
        match oind with
        | None -> eval_aux ~stats:stats c (o :: olds) (n' :: news) ctx
        | Some (ind,_) -> 
          let news' = n' :: (removen_exn ind news) in
          let olds  = o  :: (removen_exn ind olds) in 
          eval_aux ~stats:stats c olds news' ctx
      end
    else
      (* Substitutions larger than 1 variable long uses zipping and less efficient 
         assoclist facilities to delete duplicates *)
      let oldsnews = List.zip_exn olds news in
      let o', n' = 
        List.fold2_exn o n' 
          ~init:oldsnews 
          ~f:(fun on' old new' -> List.Assoc.add on' ~equal:Expr.equal old new') 
        |> List.unzip   in 
      eval_aux ~stats:stats c o' n' ctx 

(* This needs to be evaluated in the same context as was used to create the root goals *)
let eval ?debug:(debug = false) (constr : t) (ctx : Z3.context) : z3_expr =
  if debug then
    let stats = init_stats in
    let eval = eval_aux ~stats:stats constr [] [] ctx in
    let mean = (float stats.sum) /. (float stats.count)  in
    let std_dev = std_dev stats in
    Printf.printf "Showing statistics for olds and news in eval_aux: \n";
    Printf.printf "mean: %f , max: %i , std dev: %f \n %!" mean stats.maximum std_dev ;
    eval
  else
    eval_aux constr [] [] ctx


let substitute (constr : t) (olds : z3_expr list) (news : z3_expr list) : t =
  Subst (constr, olds, news)

let substitute_one (constr : t) (old_exp : z3_expr) (new_exp : z3_expr) : t =
  Subst (constr, [old_exp], [new_exp])

let update_current_regs (model : Model.model) (regs : z3_expr list) (vals : z3_expr list)
    (jmp : Jmp.t) (map : reg_map) (filter_out : z3_expr list) : reg_map =
  let registers =
    List.fold (List.zip_exn regs vals) ~init:[]
      ~f:(fun regs (reg, value) ->
          (* Manually removing mem from the list of variables being updated. *)
          if List.exists filter_out ~f:(Expr.equal reg) then
            regs
          else
            (reg, eval_model_exn model value) :: regs)
  in
  (* TODO: Figure out why we shouldn't overwrite the register values if the
     jmp is already in the map. *)
  match Jmp.Map.add map ~key:jmp ~data:registers with
  | `Ok reg_map -> reg_map
  | `Duplicate -> map

let get_refuted_goals ?filter_out:(filter_out = []) (constr : t)
    (solver : Z3.Solver.solver) (ctx : Z3.context) : refuted_goal seq =
  let model = get_model_exn solver in
  let rec worker (constr : t) (current_path : path) (current_registers : reg_map)
      (olds : z3_expr list) (news : z3_expr list) : refuted_goal seq =
    match constr with
    | Goal g ->
      let goal_val = Expr.substitute g.goal_val olds news in
      let goal_res = eval_model_exn model goal_val in
      if (Z3.Boolean.is_true goal_res)
      then Seq.empty
      else if (Z3.Boolean.is_false goal_res)
      then Seq.singleton
          { goal = { g with goal_val = goal_val };
            path = current_path;
            reg_map = current_registers }
      else
        failwith (Format.sprintf "get_refuted_goals: Unable to resolve %s" g.goal_name)
    | ITE (jmp, cond, c1, c2) ->
      let cond_val = Expr.substitute cond olds news in
      let cond_res = eval_model_exn model cond_val in
      let current_registers = update_current_regs
          model olds news jmp current_registers filter_out in
      if Z3.Boolean.is_true cond_res
      then
        let current_path = Jmp.Map.set current_path ~key:jmp ~data:true in
        worker c1 current_path current_registers olds news
      else if Z3.Boolean.is_false cond_res
      then
        let current_path = Jmp.Map.set current_path ~key:jmp ~data:false in
        worker c2 current_path current_registers olds news
      else
        failwith (Format.sprintf "get_refuted_goals: Unable to resolve branch \
                                  condition %s at %s"
                    (Z3.Expr.to_string cond_res)
                    (jmp |> Term.tid |> Tid.to_string))
    | Clause (hyps, concs) ->
      let hyps_false =
        let hyp_vals =
          List.map hyps ~f:(fun h -> eval_model_exn model (eval_aux h olds news ctx)) in
        if (List.for_all hyp_vals ~f:(fun e -> Z3.Boolean.is_true e || Z3.Boolean.is_false e))
        then (List.exists hyp_vals ~f:Z3.Boolean.is_false)
        else failwith "Unexpected Expression processing Clause"
      in
      if hyps_false then
        Seq.empty
      else
        List.fold concs ~init:Seq.empty ~f:(fun accum c ->
            Seq.append (worker c current_path current_registers olds news) accum)
    | Subst (e, o, n) ->
      let n' = List.map n ~f:(fun x -> Expr.substitute x olds news |> eval_model_exn model) in
      let oldsnews = List.zip_exn olds news in
      let o', n' =  
        List.fold2_exn o n' 
          ~init:oldsnews
          ~f:(fun on' old new' -> List.Assoc.add on' ~equal:Expr.equal old new') 
        |> List.unzip   in 
      worker e current_path current_registers o' n' (* (olds @ o) (news @ n') *)
  in
  worker constr Jmp.Map.empty Jmp.Map.empty [] []


(* stats, get_stats and print_stats are all used for debuggin purposes *)
type stats = {
  mutable goals : int;
  mutable ites : int;
  mutable clauses : int;
  mutable subs : int
}

let rec get_stats (t : t) (zstats :stats) : unit =
  match t with
  | Goal _ ->
    zstats.goals <- (zstats.goals + 1)
  | ITE (_, _, c1, c2) ->
    (get_stats  c1 zstats;
     get_stats c2 zstats;
     zstats.ites <- zstats.ites + 1)
  | Clause (hyps, concs) ->
    ( List.iter hyps ~f:(fun l -> (get_stats l zstats)) ;
      List.iter concs ~f:(fun l -> (get_stats l zstats)) ;
      zstats.clauses <- zstats.clauses + 1)
  | Subst (c, _, _) ->
    (get_stats c zstats;
     zstats.subs <- zstats.subs + 1)

let print_stats (t : t) : unit =
  let z = {goals = 0; ites = 0 ; clauses = 0; subs = 0} in
  (get_stats t z;
   Printf.printf "Showing constr.t statistics: \n ";
   Printf.printf "goals: %i , ites: %i, clauses: %i, subs: %i, \n %!"
     z.goals z.ites z.clauses z.subs )

let trivial (ctx : Z3.context) : t =
  ctx
  |> Z3.Boolean.mk_true
  |> mk_goal "true"
  |> mk_constr
