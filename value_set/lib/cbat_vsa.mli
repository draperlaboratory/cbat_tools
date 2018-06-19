open Core_kernel.Std
open Bap.Std
open Graphlib.Std

module WordSet = Cbat_clp_set_composite

module AI = Cbat_ai_representation

type vsa_sol = (tid, AI.t) Solution.t

val precond : Cbat_ai_representation.t tag

val denote_def : def term -> AI.t -> AI.t

val denote_defs : blk term -> AI.t -> AI.t

val denote_imm_exp : exp -> AI.t -> (WordSet.t, Type.error) Result.t

val denote_mem_exp : exp -> AI.t -> (Cbat_ai_memmap.t, Type.error) Result.t

val denote_block : (sub:tid -> AI.t -> target:tid -> AI.t) ->
  program term -> source:tid -> AI.t -> target:tid -> AI.t

val reachable_jumps : AI.t -> jmp term seq -> jmp term seq

val init_sol : ?entry:AI.t ->  sub term -> vsa_sol

val static_graph_vsa : tid list -> Program.t -> Sub.t -> vsa_sol -> vsa_sol
val load : sub term -> vsa_sol option
