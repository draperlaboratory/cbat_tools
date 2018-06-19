module Map = Core_kernel.Std.Map
module Option = Core_kernel.Std.Option
module Sexp = Core_kernel.Sexp
module Sexpable = Core_kernel.Sexpable
module Fn = Core_kernel.Std.Fn
module Value = Bap.Std.Value
module Lattice = Cbat_lattice_intf
module BL = Lattice.BoolLattice

(* An (indexed) Map lattice represents the lifting of an (indexed) complete
   lattice to a finite map onto elements of that (indexed) lattice. It
   includes the ability to map "the rest" of the elements to either top or
   bottom in the underlying (indexed) complete lattice.
*)

module type S_indexed = sig

  module Key : Sexpable.S
  module Val : Lattice.S_indexed

  type t
  type idx

  include Lattice.S_indexed with type t := t and type idx := idx

  (* replaces the value at the given key with the meet of it
     and the new input value.
  *)
  val meet_add : t -> key:Key.t -> data:Val.t -> t
  (* replaces the value at the given key with the join of it
     and the new input value.
  *)
  val join_add : t -> key:Key.t -> data:Val.t -> t
  (* replaces the value at the given key with the new input value. *)
  val add : t -> key:Key.t -> data:Val.t -> t

  (* retrieves the value mapped to by the map. Note that this
     always gets a value since there is a default (either top or bottom).
  *)
  val find : Val.idx -> t -> Key.t -> Val.t

end

module type S = sig
  module Key : Sexpable.S
  module Val : Lattice.S_indexed

  type t

  include Lattice.S with type t := t

  (* replaces the value at the given key with the meet of it
     and the new input value.
  *)
  val meet_add : t -> key:Key.t -> data:Val.t -> t
  (* replaces the value at the given key with the join of it
     and the new input value.
  *)
  val join_add : t -> key:Key.t -> data:Val.t -> t
  (* replaces the value at the given key with the new input value. *)
  val add : t -> key:Key.t -> data:Val.t -> t

  (* retrieves the value mapped to by the map. Note that this
     always gets a value since there is a default (either top or bottom).
  *)
  val find : Val.idx -> t -> Key.t -> Val.t
end

module type S_indexed_val = sig
  type t
  module Key : Value.S
  include S_indexed with type t := t and module Key := Key
  include Value.S with type t := t
end

module type S_val = sig
  type t
  module Key : Value.S
  include S with type t := t and module Key := Key
  include Value.S with type t := t
end

(* This functor is additionally parameterized by the map used
   so that Make_indexed_val (and potentially future functors) can
   use maps with additional functionality.
*)
module Make_indexed_from_map
    (K : Map.Key)
    (M : Map.S with type Key.t = K.t)
    (L : Lattice.S_indexed)
= struct

  module Key = K
  module Val = L

  type map = L.t M.t
  type t = map option
  type idx = L.idx

  let top : t = Some M.empty
  let bottom : t = None

  let lift : (L.t M.t -> L.t M.t) -> t -> t = Fn.flip Option.(>>|)

  let lift_meet f = Option.map2 ~f

  let lift_join (f : map -> map -> map) (t1 : t) (t2 : t) : t =
    match t1, t2 with
    | Some m1, Some m2 -> Some (f m1 m2)
    | Some m1, None -> Some m1
    | None, Some m2 -> Some m2
    | None, None -> None

  let meet' (m1 : map) (m2 : map) : map =
    (* in cases where only one side has a value,
       we meet it with the otherwise of the other
    *)
    let mFunc ~key:_ vs = match vs with
      | `Left v1 -> Some v1
      | `Right v2 -> Some v2
      | `Both (v1,v2) -> Some (L.meet v1 v2)
    in
    Map.merge m1 m2 ~f:mFunc

  let meet : t -> t -> t = lift_meet meet'

  let join' ljoin (m1 : map) (m2 : map) : map =
    let mFunc ~key:_ vs = match vs with
      | `Left _ -> None (* default is top *)
      | `Right _ -> None (* default is top *)
      | `Both (v1,v2) -> Some (ljoin v1 v2)
    in
    Map.merge m1 m2 ~f:mFunc

  let join : t -> t -> t = lift_join (join' L.join)
  let widen_join = lift_join (join' L.widen_join)

  let op_add op (m : map) ~key:key ~data:data : t =
    let idx = L.get_idx data in
    let old_data = Option.value ~default:(L.top idx) (Map.find m key) in
    Option.return @@ Map.add m ~key ~data:(op data old_data)

  let lift_add op : t -> key:Key.t -> data:Val.t -> t =
    let default = fun ~key:_ ~data:_ -> None in
    Option.value_map ~default ~f:(op_add op)

  let join_add : t -> key:Key.t -> data:Val.t -> t = lift_add L.join
  let meet_add = lift_add L.meet
  let add = lift_add (fun x _ -> x)

  let find' (idx : idx) (m : map) (k : K.t) : L.t =
    Option.value ~default:(L.top idx) (Map.find m k)

  let find idx (t : t) (k : K.t) : L.t =
    Option.value_map t ~default:(L.bottom idx)
      ~f:(fun m -> find' idx m k)

  (* Strips out any top values in the map *)
  let canonize' (m : map) : map =
    let do_include v =
      let ltop = L.top (L.get_idx v) in
      not (L.equal v ltop) in
    Map.filter m ~f:do_include

  let canonize : t -> t = lift canonize'

  let precedes' (m1 : map) (m2 : map) : bool =
    let and_val_prec ~key:_ ~data (cur : bool) : bool =
      cur && match data with
      | `Both (a, b) -> L.precedes a b
      | `Left _ -> true (* precedes top *)
      | `Right b -> L.equal b (L.top (L.get_idx b)) in
    Map.fold2 m1 m2 ~init:true ~f:and_val_prec

  let precedes (t1 : t) (t2 : t) : bool =
    Option.value_map t1 ~default:true
      ~f:(fun m1 -> Option.value_map t2 ~default:false ~f:(precedes' m1))

  let equal' (e1 : map) (e2 : map) : bool =
    M.fold2 e1 e2 ~init:true ~f:begin fun ~key:_ ~data acc ->
      acc && match data with
      | `Both (a, b) -> L.equal a b
      | `Left a -> L.equal a (L.top (L.get_idx a))
      | `Right b -> L.equal b (L.top (L.get_idx b))
    end

  let equal (t1 : t) (t2 : t) : bool =
    Option.value_map t1 ~default:(not @@ Option.is_some t2)
      ~f:(fun m1 -> Option.value_map t2 ~default:false ~f:(equal' m1))

end

module Make_indexed(K : Map.Key) = Make_indexed_from_map(K)(Map.Make(K))

module type Key_val = sig
  include Map.Key
  include Value.S with type t := t
end

module Make_indexed_val(K : Key_val)(L : Lattice.S_indexed_val) = struct

  module M = Map.Make_binable(K)

  module Base = Make_indexed_from_map(K)(M)(L)

  module Key = K
  module Val = L

  type t = L.t M.t Option.t [@@deriving bin_io, compare, sexp]

  include (Base : S
           with type t := t
            and module Key := Key
            and module Val := Val)

  let pp ppf m = match Base.canonize m with
    | _ when equal m top-> Format.fprintf ppf "unknown"
    | None -> Format.fprintf ppf "unreachable"
    | Some m ->
      Format.fprintf ppf "@[<2>{@ ";
      Map.iteri m ~f:begin fun ~key ~data ->
        Format.fprintf ppf "@[<hov 1>[%a@ -> %a]@]@ "
          K.pp key
          L.pp data
      end;
      Format.fprintf ppf "}@]"

end


module Make (K : Map.Key)(L : Lattice.S) = struct
  module IL = Lattice.Free_index(L)
  include Make_indexed(K)(IL)
end

module Make_val (K : Key_val)(L : Lattice.S_val) = struct
  module IL = Lattice.Free_index_val(L)
  include Make_indexed_val(K)(IL)
end
