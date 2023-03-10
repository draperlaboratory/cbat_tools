(***************************************************************************)
(*                                                                         *)
(*  Copyright (C) 2018/2019 The Charles Stark Draper Laboratory, Inc.      *)
(*                                                                         *)
(*  This file is provided under the license found in the LICENSE file in   *)
(*  the top-level directory of this project.                               *)
(*                                                                         *)
(*  This work is funded in part by ONR/NAWC Contract N6833518C0107.  Its   *)
(*  content does not necessarily reflect the position or policy of the US  *)
(*  Government and no official endorsement should be inferred.             *)
(*                                                                         *)
(***************************************************************************)

(** 

    When CBAT finds a countermodel, this module enables CBAT to write files 
    containing control flow graphs (CFGs) for the functions under analysis. 
    Execution paths that the countermodel induces are depicted as highlighted 
    CFG edges. CFGs are written in the Graphviz DOT format so that they can
    be rendered by any DOT viewer.

*)
open Bap.Std

(** Given two subroutines and a refuted goal produced by comparatively
    analyzing them, compute a pair of sets containing the subroutines' 
    CFG edges that are exercised by the WP-produced countermodel. *)
val taken_edges_of_refuted_goal :
  Constraint.refuted_goal
  -> Sub.t
  -> Sub.t
  -> Graphs.Ir.Edge.Set.t * Graphs.Ir.Edge.Set.t

(** Write CFGs for two functions in which execution paths induced by a
    CBAT-generated countermodel are highlighted. 

    Given a sequence of refuted goals produced by a comparative analysis of 
    two subroutines [f] and [g], write CFGs for [f] and [g] to [f_out] and 
    [g_out] (respectively) in which the CFGs paths that correspond to the first 
    refuted goal are highlighted. *) 
val pp_cfg_path_fst_refuted_goal : 
  Constraint.refuted_goal seq
  -> f:Sub.t
  -> g:Sub.t
  -> f_out:string
  -> g_out:string
  -> unit
