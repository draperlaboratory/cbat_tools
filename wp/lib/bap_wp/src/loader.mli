open Bap.Std
open Bap_core_theory

val registers : (Theory.Semantics.cls, Var.Set.t) KB.slot

val intrinsic : (Theory.Semantics.cls, bool option) KB.slot
