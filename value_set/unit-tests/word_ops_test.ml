(***************************************************************************)
(*                                                                         *)
(*  Copyright (C) 2018 The Charles Stark Draper Laboratory, Inc.           *)
(*                                                                         *)
(*  This file is provided under the license found in the LICENSE file in   *)
(*  the top-level directory of this project.                               *)
(*                                                                         *)
(*  This work is funded in part by ONR/NAWC Contract N6833518C0107.  Its   *)
(*  content does not necessarily reflect the position or policy of the US  *)
(*  Government and no official endorsement should be inferred.             *)
(*                                                                         *)
(***************************************************************************)

include Bap.Std

open OUnit2

module W = Word

open Cbat_word_ops

let be_silent = Array.length Sys.argv > 1

let print = if be_silent then fun _ -> ()  else print_string

let rec power x n =
  match n with
  | 0 -> 1
  | 1 -> x
  | _ -> x * (power x (n - 1))

let wd64 = W.of_int ~width:64
let wd32 = W.of_int ~width:32

let word_list startlist : word list =
  let rec gen_segment e l = let open !W in
    match l with
    | [] -> []
    | e':: l' -> (e * e')::(e + e')::
                 (W.logand e e')::(gen_segment e l')
  in List.fold_left (fun acc elem -> (gen_segment elem startlist) @ acc)
    startlist startlist

let take_at_most n =
  let rec take_at_most_acc n acc = function
    | [] -> acc
    | h::l -> if n > 0 then take_at_most_acc (n - 1) (h::acc) l
      else acc
  in
  take_at_most_acc n []

;;
print"Generating test lists\n";;

let testlist_64 = wd64 0 :: word_list
    [wd64 5; wd64 (-34); wd64 13214; wd64 123200300; wd64 (-1421421553)]
;;
print "64-bit Test list generated\n";;
let testlist_32 = wd32 0 :: word_list
    [wd32 5; wd32 (-34); wd32 13214; wd32 123200; wd32 (-141553)]
;;
print "32-bit Test list generated\n";;



let test_bounded_lcm_gcd _ =
  let two_exp_16_32 = W.lshift (W.one 32) (W.of_int 16 ~width:32) in
  let test_words w1 w2 =
    let gcd = bounded_gcd w1 w2 in
    match bounded_lcm w1 w2 with
    | None ->
      if W.is_zero w1 then assert_equal gcd  w2
      else if W.is_zero w2 then assert_equal gcd w1
      else OUnit2.assert_failure "lcm returned None when a solution exists";
    | Some lcm ->
      let prod = W.mul w1 w2 in
      let rem = W.modulo prod lcm in
      let cp1 = W.div w1 gcd in
      let cp2 = W.div w2 gcd in
      if W.(<) w1 two_exp_16_32 && W.(<) w2 two_exp_16_32 then
        assert_bool "Remainder is 0" (W.is_zero rem);
      assert_bool "gcd < first argument" (W.(<=) gcd w1);
      assert_bool "gcd < second argument" (W.(<=) gcd w2);
      let lcm_from_gcd1 = W.mul w1 cp2 in
      let lcm_from_gcd2 = W.mul w2 cp1 in
      assert_equal lcm_from_gcd1 lcm;
      assert_equal lcm_from_gcd2 lcm;
  in
  List.iter (fun w -> List.iter (test_words w) testlist_64) testlist_64;
  List.iter (fun w -> List.iter (test_words w) testlist_32) testlist_32;
;;

let test_bounded_diophantine _ =
  let test a b c =
    match bounded_diophantine a b c with
    | None -> (); (*TODO*)
    | Some (x, y) ->
      let c_sub_ax = W.sub c (W.mul a x) in
      (* by = c - ax mod (2^sz)
         Note: the above equation is a linear congruence and has
         a solution if d = gcd(b, 2^sz) and d | (c - ax)
      *)
      let (_, twos) = factor_2s b in
      let d = if twos = 0
        then wd64 1
        else W.lshift (wd64 1) (wd64 (twos - 1)) in
      assert_bool "c - ax % d = 0" (W.is_zero (W.modulo c_sub_ax d));
      assert_equal c_sub_ax (W.mul y b);
      (); (*TODO*)
  in
  List.iter (fun a ->
      List.iter (fun b ->
          List.iter (fun c -> test a b c)
            (take_at_most 50 testlist_64))
        (take_at_most 50 testlist_64))
    (take_at_most 50 testlist_64)
;;

let test_lead_1_bit =
  let test w zeros =
    let width = W.bitwidth w in
    let wd_plus_1 = W.of_int ~width:(width + 1) in
    let hi_bit = W.lshift (wd_plus_1 1) (wd_plus_1 width) in
    let w' = W.extract_exn ~hi:width w in
    let test_word = W.extract_exn ~hi:(width + 1 + zeros) (W.logor w' hi_bit) in
    match lead_1_bit test_word with
    | None -> failwith (Printf.sprintf "Failed to find any 1-bits in nonzero word %s\n"
                          (W.to_string test_word))
    | Some res ->
      assert_equal res width in
  let rec test_n_to_10 n w ctx =
    if n <= 10 then begin
      test w n;
      test_n_to_10 (n + 1) w ctx
    end in
  List.map (fun w -> "Testing lead_1_bit">::test_n_to_10 0 w)
    (take_at_most 100 testlist_32)
  |> List.cons ("no 1 bit of 0:53">::(fun _ -> assert_equal (lead_1_bit (W.zero 53)) None))
  |> List.cons ("no 1 bit of 0:22">::(fun _ -> assert_equal (lead_1_bit (W.zero 22)) None))
  |> List.cons ("no 1 bit of 0:8">::(fun _ -> assert_equal (lead_1_bit (W.zero 8)) None))
;;

let test_cap_at_width =
  let test_cap_one _ =
    let one' = cap_at_width ~width:2 W.b1 in
    assert_equal (W.one 2) one' in
  let test_cap w width _ =
    let w_width = W.bitwidth w in
    let w' = cap_at_width ~width w in
    if w_width <= width then
      assert_equal(W.extract_exn ~hi:(width - 1) w) w'
    else
      let w_trunc = W.extract_exn ~hi:(width-1) w in
      let w'_ext = W.extract_exn ~hi:(w_width-1) w' in
      assert_equal (W.bitwidth w') width;
      if not @@ W.is_zero w then
        assert_bool "if input is non-zero, so is result" (not @@ W.is_zero w');
      if W.(>) w w'_ext then
        assert_bool "result bounded by lower bits" (W.(>=) w' w_trunc);
  in
  testlist_32
  |> Seq.of_list
  |> Seq.map ~f:begin fun w ->
    Seq.range 1 35
    |> Seq.map ~f:(fun width ->
        Format.sprintf "test cap at width %i" width
        >::(test_cap w width))
  end
  |> Seq.concat
  |> Seq.to_list
  |> List.cons ("cap 1">::test_cap_one)
;;

(* The [dom_size i ~width:w] is 2^i, represented as a [w]-bit word. *)
let test_dom_size =

  (* If [w > i], then [dom_size] should be 2^i, represented as
     a [w]-bit word. For instance [dom_size 3 ~width:4] should 
     return a word that is 4-bits long, which represents the int 8,
     since you can have 8 elements with 3-bit words (2^3 = 8). *)

  let check_dom (i, w) _ =
    let sz = dom_size i ~width:w in
    let int_val = W.to_int_exn sz in
    let bits = W.bitwidth sz in
    let msg = Printf.sprintf "Checking that [dom_size %d ~width:%d] is %d" i w int_val in
    assert_equal ~msg:msg ~printer:string_of_int int_val (power 2 i);
    let msg = Printf.sprintf "Checking that [dom_size %d ~width:%d] is %d-bits wide" i w bits in
    assert_equal ~msg:msg ~printer:string_of_int bits w
    in

  let dom_tests =
     List.map
     begin fun (i, w) -> 
       (Printf.sprintf "dom_size %d ~width:%d = %d as %d-bit word" i w i w)>::(check_dom (i, w))
     end
     [(1, 2); (2, 3); (2, 32); (3, 4); (3, 8); (4, 5); (8, 32); (60, 61);]
     in

  (* If [i = w], then [dom_size] should be 0. For example,
     2^3 = 8, since you can represent 8 elements with 3-bits.
     However, the highest number you can represent with 3-bits
     is 7 [b111], so if you try to represent 8 [b1000] with 3 bits,
     it wraps around to 0 [b000]. *)

  let check_zero i _ =
    let sz = dom_size i ~width:i in
    let msg = Printf.sprintf "Checking that [dom_size %d ~width:%d] = 0" i i in
    assert_bool msg (W.is_zero sz)
    in

  let zero_tests =
    List.map
    begin fun i -> 
      (Printf.sprintf "dom_size %d %d = 0" i i)>::(check_zero i)
    end
    [1; 2; 3; 4; 7; 8; 32; 64; 100; 12350; 16383;]
    in

  List.flatten [dom_tests; zero_tests]
;;

let all_tests =
  "word operation tests">:::[
    "test cap_at_width">:::test_cap_at_width;
    "test lead_1_bit">:::test_lead_1_bit;
    "test bounded_diophantine">::test_bounded_diophantine;
    "test lcm and gcd">::test_bounded_lcm_gcd;
    "test dom_size">:::test_dom_size;
  ]
