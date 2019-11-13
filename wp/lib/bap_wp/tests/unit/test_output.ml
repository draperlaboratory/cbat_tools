open !Core_kernel
open OUnit2
open Bap_wp
open Output



let test_get_model (test_ctx : test_ctxt) : unit =
  let ctx = Z3.mk_context [] in 
  let solver = Z3.Solver.mk_solver ctx None in 
  let three = Z3.BitVector.mk_numeral ctx "3" 64 in
  let four = Z3.BitVector.mk_numeral ctx "4" 64 in
  let bvsort = Z3.BitVector.mk_sort ctx 64 in 
  let f =  Z3.Z3Array.mk_const_s ctx "f" bvsort bvsort in 
  let c' = Z3.Boolean.mk_eq ctx (Z3.Z3Array.mk_select ctx f three) four in
  let c'' = Z3.Boolean.mk_eq ctx (Z3.Z3Array.mk_select ctx f four) three in
  let () = Z3.Solver.add solver [c' ; c''] in
  match Z3.Solver.check solver [] with
  | Z3.Solver.UNKNOWN -> assert_failure "Solver Status UNKNOWN"
  | Z3.Solver.UNSATISFIABLE -> assert_failure "Solver Status UNSAT"
  | Z3.Solver.SATISFIABLE ->
    match Z3.Solver.get_model solver with
    | Some(model) -> 
      let decls = Z3.Model.get_decls model |> List.filter ~f:(fun decl -> (Z3.Symbol.to_string (Z3.FuncDecl.get_name decl)) = "f") in
      let f_decl = Option.value_exn (List.hd decls) in
      let f_interp = Option.value_exn (Z3.Model.get_const_interp model f_decl) in
      let mem_model = extract_array f_interp in
      assert_equal (List.hd_exn mem_model.model) (three,four) ~ctxt:test_ctx ~cmp:(fun (e1,e2) (n1,n2) -> (Z3.Expr.equal e1 n1) && (Z3.Expr.equal e2 n2) )
    | None       -> assert_failure "No Model Found"

let suite = [
  "Get Memory Model"              >:: test_get_model;
]