open Bap.Std

(**
   This module implements CLP-sets, as described (under the name "strided interval sets") in
   "(State of) The Art of War: Offensive Techniques in Binary Analysis"
*)

type t [@@deriving bin_io, sexp]

include Cbat_wordset_intf.S with type t := t

val intersect_generic : (module Cbat_wordset_intf.S with type t = 'ws) ->  t -> 'ws -> t

val overlap_generic : (module Cbat_wordset_intf.S with type t = 'ws) ->  t -> 'ws -> bool
