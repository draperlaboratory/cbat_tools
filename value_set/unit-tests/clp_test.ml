include Bap.Std
open OUnit2
open Cbat_word_ops
open Test_utils
module Option = Core_kernel.Std.Option
module Fn = Core_kernel.Std.Fn


module W = Word
module Clp = Cbat_clp

module Make(WordSet : Cbat_wordset_intf.S)
    (Conv : sig val of_clp : Cbat_clp.t -> WordSet.t end) =
struct

  let create ?width ?step ?cardn b = Conv.of_clp @@
    Clp.create ?width ?step ?cardn b

  let test_of_list _ =
    test_clps_32
    |> List.filter (fun p -> W.(<) (Clp.cardinality p) (W.of_int 400 ~width:33))
    |> List.iter begin fun p ->
      let p = Conv.of_clp p in
      let width = WordSet.bitwidth p in
      let p' = WordSet.iter p
               |> WordSet.of_list ~width in
      assert_equal ~cmp:WordSet.equal p p';
    end

  let test_min_max_elem ctxt =
    List.iter begin fun p ->
      let p = Conv.of_clp p in
      let open Monads.Std.Monad.Option.Syntax in
      Option.value ~default:() begin
        WordSet.min_elem p >>= fun min_e ->
        WordSet.max_elem p >>= fun max_e ->
        if W.(<) (WordSet.cardinality p) (W.of_int ~width:65 1000) then begin
          logf ctxt `Info "Checking elements of clp"(* TODO: WordSet.pps p*);
          List.iter begin fun w ->
            assert_bool "all elements are at least the min elem" (W.(<=) min_e w);
            assert_bool "all elements are at most the max elem" (W.(>=) max_e w)
          end (WordSet.iter p);
          !!() end
        else begin
          let step_guess = W.sub min_e max_e in
          let max_cardn = W.ones 65 in
          let inf_guess : WordSet.t = create min_e ~step:step_guess ~cardn:max_cardn in
          let p_cardn = WordSet.cardinality p in
          let two = W.of_int 2 ~width:(W.bitwidth p_cardn) in
          if WordSet.precedes p inf_guess && W.(>) p_cardn two then begin
            logf ctxt `Info "Checking ends of clp"(* TODO: WordSet.pps p*);
            assert_bool "step guessed correctly for one direction"
              (WordSet.elem (W.add min_e step_guess) p ||
               WordSet.elem (W.sub max_e step_guess) p);
          end; !!()
        end
      end
    end test_clps_64


  let testUnion _ =
    let wd = W.of_int ~width:32 in
    let wdp = W.of_int ~width:33 in
    let x = create (wd 23) in
    assert_bool "23 in {23} (singleton check)"
      (WordSet.elem (wd 23) x);
    let y = create (wd 35) in
    assert_bool "35 in {35} (singleton check)"
      (WordSet.elem (wd 35) y);
    let w = WordSet.union x y in
    assert_bool "23 in {23} U {35}" (WordSet.elem (wd 23) w);
    assert_bool "35 in {23} U {35}"  (WordSet.elem (wd 35) w);
    let ww = (WordSet.union w w) in
    assert_bool "{23} U {35} U {23} U {35} = {23} U {35}"
      (WordSet.equal w ww);
    let m = create (wd 0xfff) ~step:(wd 32) ~cardn:(wdp 60) in
    let mw = (WordSet.union w m) in
    assert_equal ~cmp:WordSet.equal mw (WordSet.union m w);
    assert_bool "{23} <= {23, 35}" (WordSet.precedes x w);
    assert_bool "{23} <= {23, 35} U m" (WordSet.precedes x mw);
    assert_bool "{23, 35} <= {23, 35} U m" (WordSet.precedes w mw);
    List.fold_left (fun _ w ->
        assert_bool "m-elem in m U {23,35}" (WordSet.elem w mw))
      () (WordSet.iter m);
    assert_bool "m <= m U {23, 35}" (WordSet.precedes m mw);
    let bot = WordSet.bottom 32 in
    List.iter begin fun w ->
      let w = Conv.of_clp w in
      let w1 = WordSet.union w bot in
      let w2 = WordSet.union bot w in
      assert_equal ~cmp:WordSet.equal w w1;
      assert_equal ~cmp:WordSet.equal w w2
    end test_clps_32;
    let pt1 = create (wd 0xFFFFFFF2) ~step:(wd 8) ~cardn:(wdp 2) in
    let pt2 = create (wd 2) ~step:(wd 8) ~cardn:(wdp 997) in
    let pt1_u_pt2_expected = create (wd 0xFFFFFFF2) ~step:(wd 8) ~cardn:(wdp 999) in
    let pt12_actual = WordSet.union pt1 pt2 in
    assert_equal ~cmp:WordSet.equal pt1_u_pt2_expected pt12_actual;
    let addr1 = create (W.of_int ~width:64 0x400106) in
    let addr2 = create (W.of_int ~width:64 0x4000e0) in
    let addr_both = WordSet.union addr1 addr2 in
    let addr_both_expected = create ~width:64 (wd 0x4000e0) ~step:(wd 0x26) ~cardn:(wd 2) in
    assert_equal ~cmp:WordSet.equal addr_both addr_both_expected




  let testAdd =
    let wd = W.of_int ~width:32 in
    let testAddSingles w1 w2 _ : unit =
      let p1 = create w1 in
      let p2 = create w2 in
      let sum1 = WordSet.add p1 p2 in
      let sum2 = WordSet.add p2 p1 in
      assert_equal ~cmp:WordSet.equal sum1 sum2;
      assert_bool "w1 + w1 in {w1} + {w2}"
        (WordSet.elem (W.add w1 w2) sum1);
      assert_equal (WordSet.iter sum1) [W.add w1 w2] in
    let testAddClps (p1,p2) _ : unit =
      let sum1 = WordSet.add p1 p2 in
      let sum2 = WordSet.add p2 p1 in
      assert_equal ~cmp:WordSet.equal sum1 sum2;
      List.fold_left (fun _ w ->
          let add_single = WordSet.add (create w) p1 in
          assert_bool "{w} + p <= {..., w, ...} + p"
            (WordSet.precedes add_single sum1);
          List.fold_left (fun _ w' ->
              assert_bool "if w in p, w' in p' then w + w' in p + p'"
                (WordSet.elem (W.add w w') sum1))
            () (WordSet.iter p1))
        () (WordSet.iter p2)
    in
    let w = create (wd (-556)) ~step:(wd 30) ~cardn:(wd 999) in
    let x = create (wd 45) ~step:(wd 0) ~cardn:(wd 9) in
    let y = create (wd 0) ~step:(wd 24) ~cardn:(wd 5) in
    let z = create (wd 11) ~step:(wd 4) ~cardn:(wd 11) in
    [
      "test {12} + {67}">::testAddSingles (wd 12) (wd 67);
      "test {-5} + {2222}">::testAddSingles (wd (-5)) (wd 2222);
      "test {0} + {11235}">::testAddSingles (wd 0) (wd 11235);
      "test {5435} + {432493284}">::testAddSingles (wd 5435) (wd 432493284);
      "test w + x">::testAddClps(w,x);
      "test w + x">::testAddClps(w,y);
      "test w + x">::testAddClps(w,z);
      "test w + x">::testAddClps(x,y);
      "test w + x">::testAddClps(x,z);
      "test w + x">::testAddClps(y,z);
    ]

  let iter_op_elem p_to_iter op containing_p =
    List.fold_left (fun _ w ->
        assert_bool "op(elem) is in CLP" (WordSet.elem (op w) containing_p))
      () (WordSet.iter p_to_iter)
  ;;

  let testNeg =
    let wd = W.of_int ~width:32 in
    let testNegClp p _ : unit =
      let res = WordSet.neg p in
      let orig = WordSet.neg res in
      assert_equal ~cmp:WordSet.equal p orig;
      assert_equal ~cmp:WordSet.equal orig p;
      iter_op_elem p W.neg res;
      iter_op_elem res W.neg p
    in
    let w = create (wd (-56)) ~step:(wd 5) ~cardn:(wd 44) in
    let x = create (wd 68) ~step:(wd 0) ~cardn:(wd 3) in
    let v = create (wd 0) ~step:(wd 24) ~cardn:(wd 5) in
    let y = create (wd (-14)) ~step:(wd 2) ~cardn:(wd 0) in
    let z = create (wd 27527) ~step:(wd 4) ~cardn:(wd 11) in
    [
      "test negation of v">::testNegClp v;
      "test negation of w">::testNegClp w;
      "test negation of x">::testNegClp x;
      "test negation of y">::testNegClp y;
      "test negation of z">::testNegClp z;
    ]


  let testNot =
    let wd = W.of_int ~width:32 in
    let testNotClp p _ : unit =
      let res = WordSet.lnot p in
      let orig = WordSet.lnot res in
      assert_equal ~cmp:WordSet.equal p orig;
      assert_equal ~cmp:WordSet.equal orig p;
      iter_op_elem p W.lnot res;
      iter_op_elem res W.lnot p
    in
    let w = create (wd (-56)) ~step:(wd 5) ~cardn:(wd 44) in
    let x = create (wd 68) ~step:(wd 0) ~cardn:(wd 3) in
    let v = create (wd 0) ~step:(wd 24) ~cardn:(wd 5) in
    let y = create (wd (-14)) ~step:(wd 2) ~cardn:(wd 0) in
    let z = create (wd 27527) ~step:(wd 4) ~cardn:(wd 11) in
    [
      "test logical negation of v">::testNotClp v;
      "test logical negation of w">::testNotClp w;
      "test logical negation of x">::testNotClp x;
      "test logical negation of y">::testNotClp y;
      "test logical negation of z">::testNotClp z;
    ]


  let testIntersect =
    let wd = W.of_int ~width:32 in
    let testAbsorption p1 p2 _ : unit =
      let un = WordSet.union p1 p2 in
      let p1' = WordSet.intersection un p1 in
      let p1'' = WordSet.intersection p1 un in
      let p2' = WordSet.intersection un p2 in
      let p2'' = WordSet.intersection p2 un in
      (*
      let info () =
        (Format.asprintf
           "@[<2>@[<hov>p1@ = %a@]@ @[<hov>p2@ = %a@]@ "
           WordSet.pp p1
           WordSet.pp p2)
        ^(Format.asprintf
            "@[<hov>un@ = p1 U p2@ = %a@]@ "
            WordSet.pp un)
        ^(Format.asprintf
            "@[<hov>int1@ = un ^ p1@ = %a@]@ @[<hov>int1'@ = p1 ^ un@ = %a@]@ "
            WordSet.pp p1'
            WordSet.pp p1'')
        ^(Format.asprintf
            "@[<hov>int2@ = un ^ p2@ = %a@]@ @[<hov>int2'@ = p2 ^ un@ = %a@]"
            WordSet.pp p2'
            WordSet.pp p2'') in
      logf ctx `Info info () ; TODO: finish  logging *)
      assert_bool "p1 contains un ^ p1 = int1"
        (WordSet.precedes p1' p1);
      assert_bool "p1 contains p1 ^ un = int1'"
        (WordSet.precedes p1'' p1);
      assert_equal ~msg:"test commutativity of intersection"
        ~cmp:WordSet.equal p1' p1'';
      assert_equal ~msg:"test commutativity of intersection"
        ~cmp:WordSet.equal p2' p2'';
      assert_equal ~msg:"test absorption"
        ~cmp:WordSet.equal p1 p1';
      assert_equal ~msg:"test absorption"
        ~cmp:WordSet.equal p2 p2';
    in
    let max_cardn = W.ones 128 in
    let w = create (wd (-56)) ~step:(wd 32) ~cardn:(wd 999) in
    let x = create (wd 45) ~step:(wd 0) ~cardn:(wd 9) in
    let y = create (wd 245) ~step:(wd 5644) ~cardn:(wd 5) in
    let z = create (wd 139) ~step:(wd 64) ~cardn:(wd 65) in
    let a = create (wd 13) ~step:(wd 4) ~cardn:max_cardn in
    let b = create (wd (-25)) ~step:(wd 1) ~cardn:max_cardn in
    let c = create (wd 654) ~step:(wd 0) ~cardn:max_cardn in
    let val1 = W.of_int ~width:64 0x40010c in
    let val2 = W.of_int ~width:64 0x40012b in
    let x' = create val2 ~step:(wd 1) ~cardn:(wd 1) in
    let y' = create val1 ~step:(wd 0x1f) ~cardn:(wd 2) in
    let int1 = WordSet.intersection x' y' in
    let int2 = WordSet.intersection y' x' in
    let test_intersect_singleton_step_1 _ =
      assert_bool "{w} intersect {w,w'} = w"
        (is_one @@ WordSet.cardinality int1);
      assert_bool "{w,w'} intersect {w} = w"
        (is_one @@ WordSet.cardinality int2);
    in
    [
      "test w x">::testAbsorption w x;
      "test w y">::testAbsorption w y;
      "test w z">::testAbsorption w z;
      "test x y">::testAbsorption x y;
      "test x z">::testAbsorption x z;
      "test y z">::testAbsorption y z;
      "test a w">::testAbsorption a w;
      "test a w">::testAbsorption a a;
      "test a w">::testAbsorption a x;
      "test a w">::testAbsorption a y;
      "test a w">::testAbsorption a z;
      "test a w">::testAbsorption a b;
      "test a w">::testAbsorption b w;
      "test a w">::testAbsorption b x;
      "test a w">::testAbsorption b y;
      "test a w">::testAbsorption b z;
      "test a w">::testAbsorption a c;
      "test a w">::testAbsorption c w;
      "test a w">::testAbsorption c x;
      "test a w">::testAbsorption c y;
      "test a w">::testAbsorption c z;
      "test a w">::testAbsorption b c;
      "test intersection of 1-step singleton">::test_intersect_singleton_step_1
    ]
  ;;


  let testAnd =
    let wd = W.of_int ~width:32 in
    let wdp = W.of_int ~width:33 in
    let testSingletons w1 w2 _ =
      let p1 = create w1 in
      let p2 = create w2 in
      let res = WordSet.logand p1 p2 in
      let res' = WordSet.logand p2 p1 in
      let target_res = create (W.logand w1 w2) in
      assert_equal ~cmp:WordSet.equal res res';
      assert_equal ~cmp:WordSet.equal res target_res in
    let testEmpty w1 _ =
      let p1 = WordSet.bottom 32 in
      let p2 = create w1 in
      let res : WordSet.t = WordSet.logand p1 p2 in
      let res' = WordSet.logand p2 p1 in
      let target_res = p1 in
      assert_equal ~cmp:WordSet.equal res res';
      assert_equal ~cmp:WordSet.equal res target_res in
    (* Note: step and stepwd should represent the same value *)
    let testOneTwo w1 (w2, step, stepwd) _ =
      let p1 = create w1 in
      let p2 = create w2 ~step ~cardn:(wd 2) in
      let res = WordSet.logand p1 p2 in
      let res' = WordSet.logand p2 p1 in
      assert_equal ~cmp:WordSet.equal res res';
      assert_bool "if |p1| = 1 and |p2| = 2 then |p1 && p2| <= 2"
        (W.(<=) (WordSet.cardinality res) (wdp 2));
      assert_bool "w1 && w2 in {w1} && {w2, w2 + s}"
        (WordSet.elem (W.logand w1 w2) res);
      assert_bool "w1 && (w2 + s) in {w1} && {w2, w2 + s}"
        (WordSet.elem (W.logand w1 (W.add w2 stepwd)) res) in
    let testOneN w1 p2 =
      let p1 = create w1 in
      let res = WordSet.logand p1 p2 in
      let res_and1 = WordSet.logand p1 res in
      Format.fprintf test_ppf "Testing %a & %a = %a = %a\n"
        WordSet.pp p1
        WordSet.pp p2
        WordSet.pp res
        WordSet.pp res_and1;
      assert(WordSet.equal res res_and1);
      if W.(<) (WordSet.cardinality p2) (wdp 1000) then
        List.iter begin fun w ->
          assert(WordSet.elem (W.logand w w1) res)
        end (WordSet.iter p2)
    in
    let w, ws, wsw = wd (-56), wd 32, wd 32 in
    let x, xs, xsw = wd 45, wd 0, wd 0 in
    let y, ys, ysw = wd 245, wd 5644, wd 5644 in
    let z, zs, zsw = wd 139, wd 64, wd 64 in
    let c, cs, csw = wd 13, wd 4, wd 4 in
    let b, bs, bsw = wd (-25), wd 1, wd 1 in
    let tests = [
      "test singleton logical and of w x">::testSingletons w x;
      "test singleton logical and of w y">::testSingletons w y;
      "test singleton logical and of w z">::testSingletons w z;
      "test singleton logical and of w c">::testSingletons w c;
      "test singleton logical and of w b">::testSingletons w b;
      "test singleton logical and of x y">::testSingletons x y;
      "test singleton logical and of x z">::testSingletons x z;
      "test singleton logical and of x c">::testSingletons x c;
      "test singleton logical and of x b">::testSingletons x b;
      "test singleton logical and of y z">::testSingletons y z;
      "test singleton logical and of y c">::testSingletons y c;
      "test singleton logical and of y b">::testSingletons y b;
      "test singleton logical and of z c">::testSingletons z c;
      "test singleton logical and of z b">::testSingletons z b;
      "test singleton logical and of c b">::testSingletons c b;
      "test logand of w with empty set">::testEmpty w;
      "test logand of x with empty set">::testEmpty x;
      "test logand of y with empty set">::testEmpty y;
      "test logand of z with empty set">::testEmpty z;
      "test logand of c with empty set">::testEmpty c;
      "test logand of b with empty set">::testEmpty b;
      "test {w} && {w, w + s_w}">::testOneTwo w (w, ws, wsw);
      "test {w} && {x, x + s_x}">::testOneTwo w (x, xs, xsw);
      "test {w} && {y, y + s_y}">::testOneTwo w (y, ys, ysw);
      "test {w} && {z, z + s_z}">::testOneTwo w (z, zs, zsw);
      "test {w} && {c, c + s_c}">::testOneTwo w (c, cs, csw);
      "test {w} && {b, b + s_b}">::testOneTwo w (b, bs, bsw);
      "test {x} && {w, w + s_w}">::testOneTwo x (w, ws, wsw);
      "test {x} && {x, x + s_x}">::testOneTwo x (x, xs, xsw);
      "test {x} && {y, y + s_y}">::testOneTwo x (y, ys, ysw);
      "test {x} && {z, z + s_z}">::testOneTwo x (z, zs, zsw);
      "test {x} && {c, c + s_c}">::testOneTwo x (c, cs, csw);
      "test {x} && {b, b + s_b}">::testOneTwo x (b, bs, bsw);
      "test {y} && {w, w + s_w}">::testOneTwo y (w, ws, wsw);
      "test {y} && {x, x + s_x}">::testOneTwo y (x, xs, xsw);
      "test {y} && {y, y + s_y}">::testOneTwo y (y, ys, ysw);
      "test {y} && {z, z + s_z}">::testOneTwo y (z, zs, zsw);
      "test {y} && {c, c + s_c}">::testOneTwo y (c, cs, csw);
      "test {y} && {b, b + s_b}">::testOneTwo y (b, bs, bsw);
      "test {z} && {w, w + s_w}">::testOneTwo z (w, ws, wsw);
      "test {z} && {x, x + s_x}">::testOneTwo z (x, xs, xsw);
      "test {z} && {y, y + s_y}">::testOneTwo z (y, ys, ysw);
      "test {z} && {z, z + s_z}">::testOneTwo z (z, zs, zsw);
      "test {z} && {c, c + s_c}">::testOneTwo z (c, cs, csw);
      "test {z} && {b, b + s_b}">::testOneTwo z (b, bs, bsw);
    ] in
    testOneN (wd (-1)) (WordSet.top 32);
    List.iter begin fun p ->
      let p = Conv.of_clp p in
      testOneN w p;
      testOneN x p;
      testOneN y p;
      testOneN z p;
      testOneN c p;
      testOneN b p;
    end test_clps_32;
    tests
  ;;

  let testOverlap =
    let wd = W.of_int ~width:32 in
    let testOffsetOne p _ =
      (* Assumes that the input is nonempty *)
      let b = match WordSet.min_elem p with Some b -> b
                                      | None -> failwith "unexpected" in
      let sb = W.succ b in
      if not (WordSet.elem sb p) then
        let one = create (wd 1) in
        let pPlus = WordSet.add p one in
        assert_bool "p does not overlap p + 1" (not (WordSet.overlap p pPlus))
    in
    let max_cardn = W.ones 128 in
    let w = create (wd (-56)) ~step:(wd 32) ~cardn:(wd 999) in
    let x = create (wd 45) ~step:(wd 0) ~cardn:(wd 9) in
    let y = create (wd 245) ~step:(wd 5644) ~cardn:(wd 5) in
    let z = create (wd 139) ~step:(wd 64) ~cardn:(wd 65) in
    let a = create (wd 13) ~step:(wd 4) ~cardn:max_cardn in
    let b = create (wd (-25)) ~step:(wd 1) ~cardn:max_cardn in
    let val1 = W.of_int ~width:64 0x40010c in
    let val2 = W.of_int ~width:64 0x40012b in
    let x' = create val2 ~step:(wd 1) ~cardn:(wd 1) in
    let y' = create val1 ~step:(wd 0x1f) ~cardn:(wd 2) in
    let test_singleton_step_1 _ =
      assert_bool "singleton overlaps pair"
        (WordSet.overlap x' y');
      assert_bool "pair overlaps singleton"
        (WordSet.overlap y' x'); in
    let test_union_overlap _ =
      List.iter begin fun p1 ->
        let p1 = Conv.of_clp p1 in
        List.iter begin fun p2 ->
          let p2 = Conv.of_clp p2 in
          if WordSet.equal p1 (WordSet.bottom (WordSet.get_idx p1)) ||
             WordSet.equal p2 (WordSet.bottom (WordSet.get_idx p2)) then begin
            assert_bool "empty set does not overlap"
              (not @@ WordSet.overlap p1 p2) end
          else
            let u = WordSet.union p1 p2 in
            assert_bool "p1 overlaps p1 U p2"
              (WordSet.overlap p1 u);
            assert_bool "p1 U p2 overlaps p1"
              (WordSet.overlap u p1);
            assert_bool "p1 U p2 overlaps p2"
              (WordSet.overlap u p2);
            assert_bool "p2 overlaps p1 U p2"
              (WordSet.overlap p2 u);
            if (WordSet.precedes p1 p2 || WordSet.precedes p2 p1) then
              assert_bool "if p1 and p2 are ordered, they overlap"
                (WordSet.overlap p1 p2);
        end test_clps_32;
        Option.iter (WordSet.min_elem p1) ~f:begin fun e1 ->
          let pe1 = create e1 in
          assert_bool "p overlaps min elem" (WordSet.overlap p1 pe1);
          assert_bool "min elem overlaps p" (WordSet.overlap pe1 p1);
        end;
      end test_clps_32;
    in
    [
      "test that x does not overlap w + 1">::testOffsetOne w;
      "test that x does not overlap x + 1">::testOffsetOne x;
      "test that x does not overlap y + 1">::testOffsetOne y;
      "test that x does not overlap z + 1">::testOffsetOne z;
      "test that x does not overlap a + 1">::testOffsetOne a;
      "test that x does not overlap b + 1">::testOffsetOne b;
      "test overlap on singletons with step 1">::test_singleton_step_1;
      "test unions overlap their components">::test_union_overlap;
    ]
  ;;

  let testCast =
    let test p _ =
      let p = Conv.of_clp p in
      let width = WordSet.bitwidth p in
      assert_equal ~msg:"cast p to its own width (unsigned)"
        ~cmp:WordSet.equal (WordSet.cast Bil.UNSIGNED width p) p;
      assert_equal ~msg:"cast p to its own width (low)"
        ~cmp:WordSet.equal (WordSet.cast Bil.LOW width p) p;
      let upcast = WordSet.cast Bil.UNSIGNED (width * 2) p in
      Format.fprintf test_ppf "Casting %a to %i is %a. Casting back\n"
        WordSet.pp p (width * 2) WordSet.pp upcast;
      assert_bool "p precedes p upcast (unsigned)"
        (WordSet.precedes p (WordSet.cast Bil.UNSIGNED width upcast));
      assert_bool "p precedes p upcast (low)"
         (WordSet.precedes p (WordSet.cast Bil.LOW width upcast));
    in
    List.map (fun p ->"testing cast">:: test p) test_clps_32
  ;;

  let testExtract =
    let test p _ =
      let p = Conv.of_clp p in
      let width = WordSet.bitwidth p in
      Seq.iter ~f:begin fun i ->
        let hi_part = WordSet.extract ~hi:(width-1) ~lo:i p in
        let lo_part = WordSet.extract ~hi:(i - 1) ~lo:0 p in
        let hi_sized = WordSet.extract ~hi:(width -1) ~lo:0 hi_part in
        let hi_positioned = WordSet.lshift hi_sized (create (W.of_int i ~width)) in
        let lo_positioned = WordSet.extract ~hi:(width -1) ~lo:0 lo_part in
        assert_equal (WordSet.bitwidth hi_positioned) (WordSet.bitwidth lo_positioned);
        let combined = WordSet.add hi_positioned lo_positioned in
        assert_bool "splitting and recombining is an approximation"
          (WordSet.precedes p combined);
      end @@ Seq.range 1 (width - 1)
    in
    List.map (fun p ->"testing extract">:: test p) test_clps_32
  ;;

  let testMul =
    let ident64 = create (W.one 64) in
    let two64 = create (W.of_int 2 ~width:64) in
    let test_ident p =
      let test _ =
        let identL = WordSet.mul ident64 p in
        let identR = WordSet.mul p ident64 in
        assert_bool "left identity holds"
          (WordSet.precedes p identL);
        assert_bool "right identity holds"
         (WordSet.precedes p identR) in
      Format.asprintf "test mul identity on %a\n"
        WordSet.pp p >:: test
    in
    let test_mul2 p =
      let test _ =
        let mul2L = WordSet.mul two64 p in
        let mul2R = WordSet.mul p two64 in
        let addself = WordSet.add p p in
        assert_equal ~cmp:WordSet.equal mul2L mul2R;
        let add_aprx_str = Format.asprintf
            "@[@[%a@ + %a@]@ approximates mul by 2@]"
            WordSet.pp mul2L WordSet.pp addself in
        assert_bool add_aprx_str
          (WordSet.precedes mul2L addself) in
      Format.asprintf "test mul by 2 on %a\n"
        WordSet.pp p >:: test
    in
    let test_mul_pair p w1 w2 =
      let pw2 = create w2 in
      let pw1 = create w1 in
      let pw = WordSet.union pw1 pw2 in
      let mul1 = WordSet.mul p pw1 in
      let mul2 = WordSet.mul p pw2 in
      let mul_both = WordSet.mul p pw in
      let mul_union_str =
        "mul by two consts then union precedes the reverse" in
      assert_bool mul_union_str
        (WordSet.precedes mul1 mul_both);
      assert_bool mul_union_str
        (WordSet.precedes mul2 mul_both)
    in
    let test_mul_pairs p =
      let test _ =
        Seq.iter ~f:begin fun w ->
          test_mul_pair p w (W.succ w);
          test_mul_pair p w (W.succ @@ W.succ w)
        end @@ Seq.map ~f:(W.of_int ~width:64)
        @@ Seq.range ~stride:117 1000000 2000000; in
      Format.asprintf
        "Test mul %a by a pair"
        WordSet.pp p >:: test
    in
    List.map begin fun p ->
      let p = Conv.of_clp p in
      [
        test_mul_pairs p;
        test_ident p;
        test_mul2 p;
      ]
    end test_clps_64
    |> List.concat

  let test_div =
    let div_le p1 p2 ctx : unit =
      let zero = Word.zero (WordSet.bitwidth p2) in
      if WordSet.elem zero p2 then
        assert_raises (Cbat_vsa_utils.NotImplemented "Clp division by zero")
          (fun () -> WordSet.div p1 p2)
      else
        let open Monads.Std.Monad.Option.Syntax in
        Option.iter ~f:(fun _ -> ()) begin
          let dv = WordSet.div p1 p2 in
          WordSet.min_elem p2 >>| WordSet.singleton >>= fun min_p2 ->
          let dv_mul = WordSet.mul min_p2 dv in
          WordSet.max_elem p1 >>= fun max_p1 ->
          WordSet.min_elem p1 >>= fun min_p1 ->
          WordSet.max_elem dv >>= fun max_dv ->
          WordSet.min_elem dv >>= fun min_dv ->
          WordSet.max_elem dv_mul >>= fun max_dv_mul ->
          WordSet.min_elem dv_mul >>| fun min_dv_mul ->
          let ws_pp () = Format.asprintf "%a" WordSet.pp in
          logf ctx `Info "Division result: %a"
            ws_pp dv;
          let max_div_str =
            Format.asprintf
              "@[%a@ >= %a@]"
              Word.pp max_p1 Word.pp max_dv in
          let min_div_str =
            Format.asprintf
              "@[%a@ >= %a@]"
              Word.pp min_p1 Word.pp min_dv in
          assert_bool max_div_str (W.(>=) max_p1 max_dv);
          assert_bool min_div_str (W.(>=) min_p1 min_dv);
          let max_div_mul_str =
            Format.asprintf
              "@[%a@ >= %a@]"
              Word.pp max_p1 Word.pp max_dv_mul in
          let min_div_mul_str =
            Format.asprintf
              "@[%a@ >= %a@]"
              Word.pp min_p1 Word.pp min_dv_mul in
          assert_bool max_div_mul_str (W.(>=) max_p1 max_dv_mul);
          assert_bool min_div_mul_str (W.(>=) min_p1 min_dv_mul);
        end
    in
    (*let mul_div_const_id p w _ =
      let pw = WordSet.singleton w in
      TODO in*)
    List.map (fun p1 ->
        let p1 = Conv.of_clp p1 in
        List.map(fun p2 ->
            let p2 = Conv.of_clp p2 in
            Format.asprintf "@.@[test min/max of@ @[%a@,/%a@]@]"
              WordSet.pp p1 WordSet.pp p2 >::
            (div_le p1 p2))
          test_clps_32)
      test_clps_32
    |> List.concat

  let testConcat =
    let test_low_single p1 w =
      let width = WordSet.bitwidth p1 in
      let p2 = create ~width w in
      let res = WordSet.concat p1 p2 in
      (*assert (W.extract_exn ~hi:(width - 1)(WordSet.cardinality res) = (WordSet.cardinality p1)); *)
      let res_hi = WordSet.extract ~hi:(2*width - 1) ~lo:width res in
      assert_bool "extract hi of concat approximates the first argument"
        (WordSet.precedes p1 res_hi) in
    let test_extract_elems p1 p2 =
      let width1 = WordSet.bitwidth p1 in
      let width2 = WordSet.bitwidth p2 in
      let width = width1 + width2 in
      let res = WordSet.concat p1 p2 in
      assert_equal (WordSet.bitwidth res) (width1 + width2);
      let p1' = WordSet.extract ~hi:(width - 1) ~lo:width1 res in
      let p2' = WordSet.extract ~hi:(width2 - 1) res in
      let check_str = Format.asprintf "%a@ <=? %a"
          WordSet.pp p1 WordSet.pp p1' in
      assert_bool check_str (WordSet.precedes p1 p1');
      let check_str = Format.asprintf "%a@ <=? %a"
          WordSet.pp p2 WordSet.pp p2' in
      assert_bool check_str (WordSet.precedes p2 p2');
    in
    let test_low_singles p _ =
      Seq.iter ~f:(test_low_single p)
      @@ Seq.map ~f:(W.of_int ~width:64)
      @@ Seq.range ~stride:117 1000000 2000000
    in
    let test_extract_elems_all p _ =
      List.iter (Fn.compose (test_extract_elems p) Conv.of_clp) test_clps_64
    in
    let low_single_list = List.map begin fun p ->
        let p = Conv.of_clp p in
        Format.asprintf "test concat hi on %a" WordSet.pp p>::(test_low_singles p)
      end test_clps_64 in
    let extract_elems_list = List.map begin fun p ->
        let p = Conv.of_clp p in
        Format.asprintf "test concat on %a" WordSet.pp p>::(test_extract_elems_all p)
      end test_clps_64 in
    List.append extract_elems_list low_single_list

  (* TODO: this test indicates that the implementation can be simplified *)
  let test_splits_by =
    let test w _ =
      List.iter begin fun p ->
        let p = Conv.of_clp p in
        if Cbat_word_ops.lt_int (WordSet.cardinality p) 100 then
          Option.iter (WordSet.min_elem p) ~f:begin fun min_e ->
            let no_split_str = Format.asprintf "%a does not split by %a"
                WordSet.pp p Word.pp w in
            let split_str = Format.asprintf "%a splits by %a"
                WordSet.pp p Word.pp w in
            if List.for_all (fun w' ->
                Word.is_zero (W.modulo (W.sub w' min_e) w))
                (WordSet.iter p)
            then assert_bool split_str @@ WordSet.splits_by p w
            else assert_bool no_split_str @@ not @@ WordSet.splits_by p w
          end
      end test_clps_64 in
    Seq.range ~start:`inclusive 1 10
    |> Seq.map ~f:(Word.of_int ~width:64)
    |> Seq.map ~f:(fun w -> Format.asprintf "test splits by %a" Word.pp w >:: test w)
    |> Seq.to_list

  let test_lshift =
    let test_seq s p _ =
      let p = Conv.of_clp p in
      let width = 64 in
      let printer = Format.asprintf "%a" WordSet.pp in
      let mulby = Seq.map s ~f:(fun i -> W.of_int ~width (1 lsl i))
                  |> Seq.to_list
                  |> WordSet.of_list ~width in
      let mul_res = WordSet.mul p mulby in
      let shiftby = Seq.map s ~f:(W.of_int ~width)
                  |> Seq.to_list
                  |> WordSet.of_list ~width in
      let lshift_res = WordSet.lshift p shiftby in
      assert_equal ~printer ~cmp:WordSet.precedes lshift_res mul_res in
    Seq.range 0 10
    |> Seq.map ~f:(fun i -> Seq.range i (i + 3))
    |> Seq.map ~f:(fun s -> List.map (test_seq s) test_clps_64)
    |> Seq.fold ~init:[] ~f:List.append
    |> List.map (fun t -> "test lshift">::t)

  let test_min_max_elem_signed ctxt =

    let make_clp w b s c =
      let b' = W.of_int b ~width:(w + 1) in
      let s' = W.of_int s ~width:(w + 1) in
      let c' = W.of_int c ~width:(w + 1) in
      Clp.create ~width:w ~step:s' ~cardn:c' b'
      in

    let clps = [
      (3, 0, 1, 8); (4, 0, 1, 16); (4, 0, 2, 8); (32, 2, 7, 50); (60, 0, 100, 1000);
      (3, -4, 1, 8); (3, -4, 2, 4); (16, -128, 3, 50); (62, -2000, 157, 1000);] 
      in

    (* Go through each CLP, and for each one, check that each element in the CLP is:
       - not greater than the maximum signed element
       - not less than the minimum signed element *)
    List.iter
      begin fun (w, b, s, c) ->

        let clp = make_clp w b s c in
        let clp_str = Printf.sprintf "CLP-%d(%d, %d, %d)" w b s c in

        let p = Conv.of_clp clp in

        let open Monads.Std.Monad.Option.Syntax in
        Option.value ~default:() begin

          WordSet.min_elem_signed p >>= fun min_e ->
          WordSet.max_elem_signed p >>= fun max_e ->

          List.iter
            begin fun wd ->

              let wd_int = W.to_int_exn wd in
              let wd_int_s = W.to_int_exn (W.signed wd) in
              let min_e_int = W.to_int_exn min_e in
              let min_e_int_s = W.to_int_exn (W.signed min_e) in
              let max_e_int = W.to_int_exn max_e in
              let max_e_int_s = W.to_int_exn (W.signed max_e) in

              let msg = 
                Printf.sprintf 
                "%s: Elem %d (%d) is less than the signed min elem %d (%d)" 
                clp_str wd_int wd_int_s min_e_int min_e_int_s 
                in
              assert_bool msg (W.(<=) (W.signed min_e) (W.signed wd));

              let msg = 
                Printf.sprintf 
                "%s: Elem %d (%d) is greater than the signed max elem %d (%d)" 
                clp_str wd_int wd_int_s max_e_int max_e_int_s 
                in
              assert_bool msg (W.(>=) (W.signed max_e) (W.signed wd))

            end
            (WordSet.iter p);

          !!()
        end

      end clps

  let all_tests = "WordSet tests">:::[
      "test creation via 'of_list'">::test_of_list;
      "test min_elem and max_elem functions">::test_min_max_elem;
      "test word-set union">::testUnion;
      "test word-set intersection">:::testIntersect;
      "test word-set addition">:::testAdd;
      "test word-set multiplication">:::testMul;
      "test word-set division">:::test_div;
      "test word-set logical and">:::testAnd;
      "test word-set negation">:::testNeg;
      "test word-set logical negation">:::testNot;
      "test word-set overlap">:::testOverlap;
      "test word-set cast">:::testCast;
      "test word-set extract">:::testExtract;
      "test word-set concat">:::testConcat;
      "test word-set splits_by">:::test_splits_by;
      "test left shift">:::test_lshift;
      "test min_ and max_elem_signed">::test_min_max_elem_signed;
    ]

end
