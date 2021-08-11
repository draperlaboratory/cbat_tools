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

   This module is used for managing BAP caches for the knowledge base and
   and project state. It contains functions for loading and saving the state
   of the knowledge base, the state of a project, the program representation
   of a binary, and the target architecture of a binary.

*)

open Bap_main
open Regular.Std

(** This module is used for creating digests, which is a cryptographic key
    for caching. In order to create a digest, the generator must first be
    called, and its output should be passed into the digest creator function for
    the appropriate cache. *)
module Digests : sig

  (** Returns a function that makes digests. *)
  val generator :
    ctxt -> filepath:string -> loader:string -> (namespace:string -> digest)

  (** Creates a digest for the knowledge cache. *)
  val knowledge : (namespace:string -> digest) -> digest

  (** Creates a digest for the project state cache. *)
  val project : (namespace:string -> digest) -> digest

  (** Creates a digest for the program cache. *)
  val program : (namespace:string -> digest) -> digest

end
