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

open !Core_kernel
include Bap.Std

module Fn = Core_kernel.Fn
module Sexp = Core_kernel.Sexp
module Option = Core_kernel.Option
module Or_error = Core_kernel.Or_error
module Result = Core_kernel.Result
module Binable = Core_kernel.Binable

module Lattice = Cbat_lattice_intf
module WordSet = Cbat_clp_set_composite
module Utils = Cbat_vsa_utils
module Map_lattice = Cbat_map_lattice
module Word_ops = Cbat_word_ops

(** We assume that all memories are byte-addressable.
    This simplifies the definition of the Val module since
    its behavior is predicated on this value. The simplest
    fix would add this integer as a parameter to all values
    despite it being constant per-map.  In practice, most
    programs are decompiled as byte-addressable
    (This is largely baked into BAP as well)
    TODO: fix this via a secondary, internal module that
    adapts its interface to deal with this.
 *)
let addressable_width = 8

module Key = struct
  (* invariant: lo <= hi
     TODO: allow empty intervals?
     TODO: use Clps/WordSets?
  *)
  type t = {lo : word; hi : word} [@@deriving bin_io, sexp]
  (* Our points are just words in the space addressable by the key *)
  type point = addr [@@deriving bin_io, sexp]


  let create ~lo ~hi : t Or_error.t =
    if lo <= hi then Result.Ok {lo; hi}
    else Or_error.error "attempted to create key with lo above hi"
        (lo, hi) (fun (lo, hi) -> Sexp.List[Word.sexp_of_t lo;
                                            Word.sexp_of_t hi])

  (* The upper point is the last (byte) address that is writable at
     this key. It corresponds to the highest address in the set.
     Note that the interval tree does not handle sets that wrap 0 well.
     It will approximate these sets as the set of all addresses.
     This behavior shoud be reasonable because, since the low part of the
     address space is typically reserved and the high part corresponds
     to the top of the stack, few pointer ranges besides top are likely to
     wrap 0.
  *)
  let upper (k : t) : point = k.hi

  (* The first writable byte is at the lowest address in the key *)
  let lower (k : t) : point = k.lo

  let sexp_of_point = Addr.sexp_of_t

  let compare_point : point -> point -> int = Addr.compare

  (* This function does not consider the widths since
     it compares the lowest writable addresses in the keys.
  *)
  let compare (k1 : t) (k2 : t) : int =
    compare_point (lower k1) (lower k2)

  let contains (k : t) (pt : point) : bool =
    Word.(<=) (lower k) pt && Word.(<=) pt (upper k)

  let overlap (k1 : t) (k2 : t) : bool =
    contains k1 (lower k2) || contains k2 (lower k1)

  let of_wordset (p : WordSet.t) : t option =
    let open Monads.Std.Monad.Option.Syntax in
    WordSet.min_elem p >>= fun lo ->
    WordSet.max_elem p >>= fun hi ->
    !!{lo; hi}

  (* Produces a key that contains all addresses in both inputs. *)
  let union (k1 : t) (k2 : t) : t =
    {lo = Addr.min (lower k1) (lower k2);
     hi = Addr.max (upper k1) (upper k2)}

  let intersection (k1 : t) (k2 : t) : t =
    {lo = Addr.max (lower k1) (lower k2);
     hi = Addr.min (upper k1) (upper k2)}


  type 'a up_to_two = [`none | `one of 'a | `two of 'a * 'a]

  (* resulting intervals may not be ordered *)
  let interval_diff (k1 : t) (k2 : t) : t up_to_two =
    if Word.(<) (lower k1) (lower k2) then
      if Word.(<) (upper k1) (lower k2) then `one k1
      else if contains k2 (upper k1) then
        `one {lo=k1.lo; hi=Addr.pred k2.lo}
      else `two ({lo=k1.lo; hi=Addr.pred k2.lo},
                 {lo=Addr.succ k2.hi; hi=k1.hi})
    else if contains k2 (lower k1) then
      if Word.(>) (upper k1) (upper k2) then
        `one {lo=Addr.succ k2.hi; hi=k1.hi}
      else `none
    else `one k1 (* lower k1 > upper k2 *)

  (* Takes an ordered sequence of key-value pairs and returns an
     ordered sequence of the gaps between them paired with the
     input value within the bounds of k.

     TODO: check all cases at the bounds (hi = 0xFFF...)
  *)
  let gaps (v : 'a) (k : t) (s : (t * 'a) seq) : (t * 'a) seq =
    (* compute what (and whether) the next lower point is *)
    let next_pt pt =
      let next = Word.succ pt in
      Option.some_if (not (Word.is_zero next)) next in
    (* given a low point to start from, generate the next element in
       the sequence.
    *)
    let running_step' pt (k',_) =
      let hi = Word.min k.hi k'.lo in
      if Word.(>) pt k.hi then Seq.Step.Done
      else if Word.(<=) pt hi then Seq.Step.Yield
          (({lo=pt; hi}, v), next_pt hi)
      else Seq.Step.Skip (next_pt (Word.max hi pt)) in
    (* computes the last gap after the input sequence ends *)
    let finishing_step' pt =
      if Word.(<=) pt k.hi then Seq.Step.Yield
          (({lo = pt; hi = k.hi}, v), next_pt k.hi)
      else Seq.Step.Done in
    Seq.unfold_with_and_finish s ~init:(Some k.lo)
      ~running_step:(Option.value_map
                       ~default:(fun _ -> Seq.Step.Done)
                       ~f:running_step')
      ~inner_finished:(fun x -> x)
      ~finishing_step:(Option.value_map
                         ~default:Seq.Step.Done
                         ~f:finishing_step')

  type side = Left | Right | Both_sides
  module Seq_ME = Seq.Merge_with_duplicates_element

  type section =
    | Left_Mid of t * t
    | Left_Right of t * t
    | Mid_Right of t * t
    | Left_Mid_Right of t * t * t


  let sections (k1 : t) (k2 : t) : side * t * ((t, t) Seq_ME.t) option =
    if Word.(<) k1.hi k2.lo then Left, k1, Some (Seq_ME.Right k2)
    else if Word.(<) k2.hi k1.lo then Right, k2, Some (Seq_ME.Left k1)
    else if Word.(<) k1.lo k2.lo then
      let res = {lo=k1.lo;hi=Word.pred k2.lo} in
      let newK1 = {lo=k2.lo;hi=k1.hi} in
      Left, res, Some (Seq_ME.Both (newK1, k2))
    else if Word.(<) k2.lo k1.lo then
      let res = {lo=k2.lo;hi=Word.pred k1.lo} in
      let newK2 = {lo=k1.lo;hi=k2.hi} in
      Right, res, Some (Seq_ME.Both (k1, newK2))
    else if Word.(<) k1.hi k2.hi then (* k1.lo = k2.lo *)
      let newK2 = {lo=Word.succ k1.hi;hi=k2.hi} in
      Both_sides, k1, Some (Seq_ME.Right newK2)
    else if Word.(<) k2.hi k1.hi then
      let newK1 = {lo=Word.succ k2.hi;hi=k1.hi} in
      Both_sides, k2, Some (Seq_ME.Left newK1)
    else (* k1.hi = k2.hi *)
      Both_sides, k1, None

  (* takes two ordered sequences of non-overlapping keys and returns
     an ordered sequence of non-overlapping keys with the side they came from.
  *)
  let seq_product (s1 : t seq) (s2 : t seq) : (side * t) seq =
    let combined = Seq.merge_with_duplicates s1 s2 ~cmp:compare in
    Seq.unfold_step ~init:combined ~f:begin fun s ->
      Option.value_map ~default:Seq.Step.Done (Seq.next s) ~f: begin
        fun (hd, tl) -> match hd with
          | Seq_ME.Left k1 -> Seq.Step.Yield ((Left, k1), tl)
          | Seq_ME.Right k2 -> Seq.Step.Yield ((Right, k2), tl)
          | Seq_ME.Both (k1, k2) ->
            let s, k, mrest = sections k1 k2 in
            let tl' = Option.fold mrest ~init:tl ~f:Seq.shift_right in
            Seq.Step.Yield ((s, k), tl')
      end
    end

  let pp ppf (k : t) = Format.fprintf ppf "@[[%a@ ...@ %a]@]" Word.pp k.lo Word.pp k.hi


end

(* Represents the values stored at each key in an internal interval tree.
   Contains a WordSet and ancillary data.
*)
module Val : sig

  type t [@@deriving bin_io, sexp, compare]

  module Idx : Lattice.S_semi with type t = WordSet.idx * endian

  include Lattice.S_indexed with type t := t and type idx = Idx.t

  val create : WordSet.t -> endian -> t

  val data : t -> WordSet.t

  val idx_equal : idx -> idx -> bool

  val is_top : t -> bool
  val is_bottom : t -> bool

  val join_at : idx -> t -> t -> t
  val meet_at : idx -> t -> t -> t

  val join_poly : t -> t -> t
  val meet_poly : t -> t -> t

  val pp : Format.formatter -> t -> unit

end = struct

  type idx = WordSet.idx * endian

  module Idx : Lattice.S_semi with type t = idx = struct

    type t = idx

    let top = 1, BigEndian

    let join (w1, e1 : t) (w2, e2 : t) : t =
      if e1 = e2 then min w1 w2, e1 else min addressable_width (min w1 w2), e1

    let widen_join = join

    let precedes (w1, e1 : t) (w2, e2 : t) : bool =
      w1 >= w2 && (w2 <= addressable_width || e1 = e2)

    let equal i1 i2 : bool = precedes i1 i2 && precedes i2 i1

    let sexp_of_t (w, e : t) : Sexp.t =
      let edstr = Word_ops.endian_string e in
      Sexp.List [Sexp.Atom (string_of_int w); Sexp.Atom edstr]

  end

  type t = {data : WordSet.t; endian : endian} [@@deriving bin_io, sexp, compare]

  let create data endian = {data; endian}

  let data (v : t) : WordSet.t = v.data

  let get_idx (v : t) : idx = WordSet.bitwidth v.data, v.endian

  let idx_equal (w1, e1 : idx) (w2, e2 : idx) : bool =
    w1 = w2 && (w1 <= addressable_width || e1 = e2)

  let lift_in (f : WordSet.t -> 'a) (v : t) : 'a = f v.data

  let lift (f : WordSet.t -> WordSet.t) (v : t) : t = {data = lift_in f v; endian = v.endian}

  let lift2_in (f : WordSet.t -> WordSet.t -> 'a) (v1 : t) (v2 : t) : 'a =
    assert (idx_equal (get_idx v1) (get_idx v2));
    f v1.data v2.data

  let lift2 (f : WordSet.t -> WordSet.t -> WordSet.t) (v1 : t) (v2 : t) : t =
    {data = lift2_in f v1 v2; endian = v1.endian}


  let top (w, e : idx) : t = {data = WordSet.top w; endian = e}
  let bottom (w, e : idx) : t = {data = WordSet.bottom w; endian = e}

  let equal = lift2_in WordSet.equal
  let precedes = lift2_in WordSet.precedes

  let join = lift2 WordSet.join
  let meet = lift2 WordSet.meet

  let widen_join = lift2 WordSet.widen_join

  let is_top = lift_in WordSet.is_top
  let is_bottom = lift_in WordSet.is_bottom

  let pp ppf (v : t) =
    Format.fprintf ppf "@[%s %a@]" (Word_ops.endian_string v.endian) WordSet.pp v.data

  (* Helper function; splits a WordSet into a sequence of WordSets of length w.
     w should be a factor of p's width.
  *)
  let segment_wordset (p : WordSet.t) (w : int) : WordSet.t seq =
    let p_sz = WordSet.bitwidth p in
    assert(w mod addressable_width = 0);
    assert(p_sz mod addressable_width = 0);
    Seq.unfold ~init:0 ~f:begin fun lo ->
      let hi = lo + (w - 1) in
      if lo >= p_sz then None
      else if hi >= p_sz then Utils.not_implemented
          "Wordset segmented by non-factor size"
      else Option.return (WordSet.extract ~hi ~lo p, hi + 1)
    end

  let reverse_seq : 'a seq -> 'a seq = Fn.compose Seq.of_list Seq.to_list_rev

  (* returns a WordSet with size at least sz
     Note: this is inaccurate in any case where step > 1
  *)
  let replicate_wordset (p : WordSet.t) (sz : int) : WordSet.t =
    let rec replicate_help (p' : WordSet.t) : WordSet.t =
      let p'_sz = WordSet.bitwidth p' in
      if p'_sz >= sz then p' else
        replicate_help (WordSet.concat p p') in
    replicate_help p

  (* Returns a sequence of values ordered from lowest address to highest *)
  (* TODO: fold into cast_seq? *)
  let cast_seq (sz, e : idx) (v : t) : WordSet.t seq =
    (* TODO: if v has size < 8, this could result in an unnecessary
       loss of precision at replication *)
    let sz = if e = v.endian then sz else addressable_width in
    let w, e = get_idx v in
    let top = Seq.singleton @@ WordSet.top sz in
    let p = replicate_wordset v.data sz in
    if WordSet.bitwidth p mod sz > 0 then Utils.not_implemented ~top
       (Printf.sprintf "%i-val cast to incompatible size %i" w sz)
    else let wordset_seq = segment_wordset p sz in
      match e with
      | BigEndian -> reverse_seq wordset_seq
      | LittleEndian -> wordset_seq

  let op_at_seq op (sz, e : idx) (v1 : t) (v2 : t) : WordSet.t seq =
    let seq1 = cast_seq (sz, e) v1 in
    let seq2 = cast_seq (sz, e) v2 in
    let sz1, _ = get_idx v1 in
    let sz2, _ = get_idx v2 in
    let seq_len = Utils.cdiv (max sz1 sz2) sz in
    let seq1 = Seq.concat @@ Seq.repeat seq1 in
    let seq2 = Seq.concat @@ Seq.repeat seq2 in
    let res_inf_seq = Seq.zip seq1 seq2 |>
                      Seq.map ~f:(fun (x,y) -> op x y) in
    Seq.take res_inf_seq seq_len


  let op_at(op : WordSet.t -> WordSet.t -> WordSet.t) (sz, e : idx) (v1 : t) (v2 : t) : t =
    let wordset_seq  = op_at_seq op (sz, e) v1 v2 in
    let wordset_of_int i = WordSet.singleton (Word.of_int ~width:sz i) in
    let place_in_result = match e with
      | LittleEndian -> fun i p ->
        let sized_p = WordSet.cast Bil.UNSIGNED sz p in
        WordSet.lshift sized_p @@ wordset_of_int @@ i * (WordSet.bitwidth p)
      | BigEndian -> fun i p ->
        let sized_p = WordSet.cast Bil.UNSIGNED sz p in
        WordSet.lshift sized_p @@ wordset_of_int @@
        (sz - (i + 1) * (WordSet.bitwidth p)) in
    wordset_seq |> Seq.mapi ~f:place_in_result
    |> Seq.reduce_exn ~f:WordSet.join
    |> fun p -> create p e

  (* Computes the op of two tree values with possibly differring indices.
     The result has the maximum of the two values' sizes. Note that this
     operation is not commutative since it has the endianness of the right
     argument.
  *)
  let op_poly (op : WordSet.t -> WordSet.t -> WordSet.t) (v1 : t) (v2 : t) : t =
    let w1, _ = get_idx v1 in
    let w2, _ = get_idx v2 in
    let sz = max w1 w2 in
    op_at op (sz, v2.endian) v1 v2

  let join_at = op_at WordSet.join
  let meet_at = op_at WordSet.meet

  let join_poly = op_poly WordSet.join
  let meet_poly = op_poly WordSet.meet

end

module IT = Interval_tree.Make_binable(Key)

module BL = Lattice.BoolLattice

type idx = {addr_width:int; addressable_width:int} [@@deriving bin_io, sexp, compare]

type itree = Val.t IT.t

type t = {itree : Val.t IT.t option; width : int}
[@@deriving bin_io, sexp, compare]

let get_idx (m : t) : idx = {addr_width = m.width; addressable_width}
let top (i : idx) : t =
  assert(i.addressable_width = addressable_width);
  {itree=Some IT.empty; width=i.addr_width}
let bottom (i : idx) : t =
  assert(i.addressable_width = addressable_width);
  {itree=None; width=i.addr_width}

(* A note on complexity: A number of the operations used internally
   are linear in the number of overlaps in the tree. Thus, some of these
   functions are quadratic or more in the number of overlaps. For efficient
   performance, the allocated abstract locations should be disjoint. However,
   the tree will still function with overlaps.
   TODO: check whether the above is still true!
*)

(* dynamic keys implementation *)
(* TODO: issues: endianness, width. Current implementation does not handle
   variable endianness or width properly. These must be addressed.
   TODO: performance: the add functions all sometimes split existing
   intervals. This might usually work, but could cause pathological blowup
 *)

(* helper function *)
let default_value (o : BL.t) (i : Val.idx) : Val.t =
  if BL.equal o BL.top then Val.top i else Val.bottom i

(* TODO: Currently, some memory entries are repeated.
   This should not affect the results, but is an unnecessary use
   of memory. Fix this.
*)
let op_add' op (m : itree) (width : int) ~key:(k : Key.t) ~data:(d : Val.t) : t =
  let ints = IT.intersections m k in
  let rest = IT.remove_intersections m k in
  let gaps = Key.gaps (Val.top (Val.get_idx d)) k ints in
  let overlaps = Seq.append gaps ints in
  let itree =
    Seq.fold overlaps ~init:rest ~f:begin fun rest (k',d') ->
      let newD = op d d' in
      let k_int = Key.intersection k k' in
      (* Update the range of the key that overlaps the add *)
      let rest = IT.add rest k_int newD in
      (* Replace the range(s) of the key that do not overlap *)
      match Key.interval_diff k' k with
      | `none -> rest
      | `one k1 -> IT.add rest k1 d'
      | `two (k1, k2) -> IT.add (IT.add rest k1 d') k2 d'
    end in
  {itree = Some itree; width}

let op_add op (m : t) : key:Key.t -> data:Val.t -> t = match m.itree with
  | None -> fun ~key:_ ~data:_ -> {itree=None; width=m.width}
  | Some t -> op_add' op t m.width

(* Adds the new value by joining it with prior overlapping values *)
let join_add : t -> key:Key.t -> data:Val.t -> t = op_add Val.join_poly

(* Adds the new value by meeting it with prior overlapping values *)
let meet_add : t -> key:Key.t -> data:Val.t -> t = op_add Val.meet_poly

(* Adds the new value by overwriting the prior value if it can only
   be written to one location and joining it with the prior
   overlapping values otherwise.
*)
let add (m : t) ~key : data:Val.t -> t =
  (* TODO: op is unsound in the case that d' is longer than d*)
  if Key.lower key = Key.upper key then op_add (fun d _ -> d) m ~key
  else join_add m ~key

(* Retrieves a WORDSET representing the set of possible values stored
   at the given key and with the given index.
*)
let find' (i : Val.idx) (m : itree) (k : Key.t) : Val.t =
  assert(fst i > 0);
  let ints = IT.intersections m k in
  let default = Val.top i in
  Option.value_map ~default (Seq.next ints) ~f: begin fun ((_,hd), _) ->
    (* Mapping back over ints will cause join_at i to be called every time.
       This ensures that the result has the correct width even when there is
       only one intersection.
    *)
    Seq.fold ints ~init:hd ~f:(fun v (k',v') ->
        let lo_key_start = min (Key.lower k) (Key.lower k') in
        let hi_key_start = max (Key.lower k) (Key.lower k') in
        let keys_aligned =
          Word.is_zero (Word.modulo (Word.sub hi_key_start lo_key_start)
                          (Word.of_int (fst i) ~width:(Addr.bitwidth lo_key_start))) in
        if keys_aligned then Val.join_at i v v' else Val.top i)
  end

let find (i : Val.idx) (m : t) (k : Key.t) = match m.itree with
  | None -> Val.bottom i
  | Some t -> find' i t k

(* Retrieves the index of values referenced at the given key. *)
let find_idx' (m : itree) (k : Key.t) : Val.idx =
  let ints = IT.intersections m k in
  let default = Val.Idx.top in
  Option.value_map ~default (Seq.next ints) ~f: begin fun ((_,hd), tl) ->
    Seq.map ~f:(Fn.compose Val.get_idx snd) tl |> Seq.fold ~init:(Val.get_idx hd) ~f:Val.Idx.join
  end

let find_idx (m : t) (k : Key.t) : Val.idx = match m.itree with
  | None -> Val.Idx.top
  | Some t -> find_idx' t k

(* Note that the behavior of precedes is non-intuitive due to the definition
   of Wordset union. Specifically, the desirable property that if (precedes m1 m2)
   returns true then for all keys k, WordSet.precedes (find idx m1 k) (find idx m2 k)
   is true DOES NOT HOLD in general. When k covers two intervals stored separately
   in both m1 and m2, find will union together the values from each memory. Since
   Wordset union chooses the smallest known approximation, one union may include values
   that the other does not.
   Since the issue arises when a key spans multiple memory intervals, the desired
   property does hold if the key represents a single point (i.e. its lower and
   upper bounds are the same).
*)
let precedes' (m1 : itree) (m2 : itree) : bool =
  let m1_seq = IT.to_sequence m1 in
  let m2_seq = IT.to_sequence m2 in
  Seq.for_all m1_seq ~f: begin fun (k, v) ->
    (* If the key overlaps a space, v must precede m2's default *)
    (IT.dominates m2 k ||
     Val.precedes v (Val.top (Val.get_idx v))) &&
    Seq.for_all (IT.intersections m2 k) ~f:begin fun (_,v') ->
      Val.precedes v v'
    end
  end &&
  Seq.for_all m2_seq ~f: begin fun (k, v) ->
    (* If the key overlaps a space, m2's default must precede v *)
    (IT.dominates m2 k ||
     Val.precedes (Val.top (Val.get_idx v)) v) &&
    Seq.for_all (IT.intersections m2 k) ~f:begin fun (_,v') ->
      Val.precedes v' v
    end
  end

let precedes (m1 : t) (m2 : t) : bool =
  assert(m1.width = m2.width);
  match m1.itree, m2.itree with
  | None, _ -> true
  | Some _, None -> false
  | Some t1, Some t2 -> precedes' t1 t2

(* TODO: canonize does not produce a unique form
   (byte-endianness, maybe more). Requires at least
   canonizing values, merging adjacent, equal values
*)
let canonize (m : t) : t =
  let width = m.width in
  let itree = Option.map m.itree ~f:(IT.filter ~f:(fun d ->
      not (Val.equal d (Val.top (Val.get_idx d))))) in
  {itree; width}

(* TODO: check *)
let equal' (m1 : itree) (m2 : itree) : bool =
  Seq.for_all (IT.to_sequence m1) ~f: begin fun (key, d1) ->
    let d2 = find' (Val.get_idx d1) m2 key in
    (* d1 = find ... m1 key since all keys are disjoint *)
    Val.equal d1 d2
  end && Seq.for_all (IT.to_sequence m2) ~f: begin fun (key, d2) ->
    let d1 = find' (Val.get_idx d2) m1 key in
    Val.equal d1 d2
  end

let equal (m1 : t) (m2 : t) : bool =
  assert(m1.width = m2.width);
  Option.equal equal' m1.itree m2.itree

(* Note that this definition of join, while sound,
   can greatly increase the size of memory.
*)
let join' (m1 : itree) (m2 : itree) : itree =
  let m1_seq = Seq.map ~f:fst (IT.to_sequence m1) in
  let m2_seq = Seq.map ~f:fst (IT.to_sequence m2) in
  let keys = Key.seq_product m1_seq m2_seq in
  Seq.fold keys ~init:IT.empty ~f: begin fun it (s, key) ->
    (* Get the best index compatible with all of the data stored at this key *)
    let idx = match s with
      | Key.Left -> find_idx' m1 key
      | Key.Right -> find_idx' m2 key
      | Key.Both_sides ->
        let idx1 = find_idx' m1 key in
        let idx2 = find_idx' m2 key in
        Val.Idx.join idx1 idx2 in
    let d1 = find' idx m1 key in
    let d2 = find' idx m2 key in
    IT.add it key @@ Val.join d1 d2
  end

let lift_join f (m1 : t) (m2 : t) : t =
  assert(m1.width = m2.width);
  match m1.itree, m2.itree with
  | Some t1, Some t2 -> {itree=Some (f t1 t2); width=m1.width}
  | Some _, None -> m1
  | None, Some _ -> m2
  | None, None -> m1 (* m1 = m2 = bottom *)

let join : t -> t -> t = lift_join join'


let widen_join' (m1 : itree) (m2 : itree) : itree =
  assert(precedes' m1 m2);
  let m2_seq = Seq.map ~f:fst (IT.to_sequence m2) in
  Seq.fold m2_seq ~init:IT.empty ~f: begin fun it key ->
    let idx = find_idx' m2 key in
    let d1 = find' idx m1 key in
    let d2 = find' idx m2 key in
    IT.add it key @@ Val.widen_join d1 d2
  end

let widen_join = lift_join widen_join'

(* Note that this definition of meet, while sound,
   can greatly increase the size of memory.
*)
let meet' (m1 : itree) (m2 : itree) : itree =
  let m1_seq = Seq.map ~f:fst (IT.to_sequence m1) in
  let m2_seq = Seq.map ~f:fst (IT.to_sequence m2) in
  let keys = Key.seq_product m1_seq m2_seq in
  Seq.fold keys ~init:IT.empty ~f: begin fun it (s, key) ->
    (* Get the best index compatible with all of the data stored at this key *)
    let idx = match s with
      | Key.Left -> find_idx' m1 key
      | Key.Right -> find_idx' m2 key
      | Key.Both_sides ->
        let idx1 = find_idx' m1 key in
        let idx2 = find_idx' m2 key in
        Val.Idx.join idx1 idx2 in
    let d1 = find' idx m1 key in
    let d2 = find' idx m2 key in
    IT.add it key @@ Val.meet d1 d2
  end

let meet (m1 : t) (m2 : t) : t =
  assert(m1.width = m2.width);
  match m1.itree, m2.itree with
  | Some t1, Some t2 -> {itree=Some (meet' t1 t2); width=m1.width}
  | None, _ -> {itree=None; width=m1.width}
  | _, None -> {itree=None; width=m1.width}

let pp ppf (m : t) : unit =
  match (canonize m).itree with
  | None -> Format.fprintf ppf "unreachable"
  | Some t ->
    Format.fprintf ppf "@[<2>----------------------------------------@ ";
    t
    |> IT.to_sequence
    |> Seq.iter ~f:(fun (k, v) -> Format.fprintf ppf "@[<hov 1>[%a@ -> %a]@]@ " Key.pp k Val.pp v);
    Format.fprintf ppf "----------------------------------------@]"
