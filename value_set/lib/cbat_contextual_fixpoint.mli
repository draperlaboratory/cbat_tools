open Graphlib.Std



(** An extension of the BAP fixpoint function that supports context-sensitive
    analysis.
*)
val fixpoint : (module Graph with type t = 'c
                              and type node = 'n) ->
  ?steps:int -> ?start:'n -> ?rev:bool ->
  ?step:(int -> 'n -> 'd -> 'd -> 'd) ->
  init:('n,'d) Solution.t ->
  equal:('d -> 'd -> bool) ->
  merge:('d -> 'd -> 'd) ->
  f:(source:'n -> 'd -> target:'n -> 'd) -> 'c -> ('n,'d) Solution.t
