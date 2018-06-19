open Bap.Std

type t

include Cbat_wordset_intf.S with type t := t

val is_top : t -> bool
val is_bottom : t -> bool

val of_clp : Cbat_clp.t -> t
