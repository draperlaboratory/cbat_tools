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

open Core_kernel.Std
open Bap.Std

(* An (indexed) Map lattice represents the lifting of an (indexed) complete
   lattice to a finite map onto elements of that (indexed) lattice. It
   includes the ability to map "the rest" of the elements to either top or
   bottom in the underlying (indexed) complete lattice.
*)

module type S_indexed = sig

  module Key : Sexpable.S
  module Val : Cbat_lattice_intf.S_indexed

  type t
  type idx

  include Cbat_lattice_intf.S_indexed with type t := t and type idx := idx

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
  module Val : Cbat_lattice_intf.S_indexed

  type t

  include Cbat_lattice_intf.S with type t := t

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

module type Key_val = sig
  include Map.Key
  include Value.S with type t := t
end

module Make_indexed_val(K : Key_val)(L : Cbat_lattice_intf.S_indexed_val) : S_val
  with module Key = K and module Val = L

module Make_indexed(K : Map.Key)(L : Cbat_lattice_intf.S_indexed) : S
  with module Key = K and module Val = L

module Make_val(K : Key_val)(L : Cbat_lattice_intf.S_val) : S_val
  with module Key = K and module Val = Cbat_lattice_intf.Free_index_val(L)

module Make(K : Map.Key)(L : Cbat_lattice_intf.S) : S
  with module Key = K and module Val = Cbat_lattice_intf.Free_index(L)
