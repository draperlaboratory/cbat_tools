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
   of a binary, and the architecture of a binary.

*)

open Bap_main
open Bap.Std
open Regular.Std

(** This module is used for creating digests, which is a cryptographic key
    for caching. In order to create a digest, the generator must first be
    called, and its output should be passed into the digest creator function for
    the appropriate cache. *)
module Digests : sig

  (** Returns a function that makes digests. *)
  val get_generator :
    ctxt -> filepath:string -> loader:string -> (namespace:string -> digest)

  (** Creates a digest for the knowledge cache. *)
  val knowledge : (namespace:string -> digest) -> digest

  (** Creates a digest for the project state cache. *)
  val project : (namespace:string -> digest) -> digest

end

(** A cache containing persistent information stored in the Knowledge Base. *)
module Knowledge : sig

  (** Loads knowledge (if any) from the cache. *)
  val load : digest -> unit

  (** Saves knowledge in the cache. *)
  val save : digest -> unit

end

(** A cache containing the initial state of a project for loading in binaries
    as a Project.t *)
module Project : sig

  (** Loads project state (if any) from the cache. *)
  val load : digest -> Project.state option

  (** Saves project state in the cache. *)
  val save : digest -> Project.state -> unit

end

(** This module contains functions for interacting with a binary's Program.t,
    which is BAP's representation of the program in BIR after disassembly. This
    program is stored in the knowledge base cache, and will persist on different
    runs of WP on the same unchanged binary given the same flags are used for
    disassembly. *)
module Program : sig

  (** [load filename] obtains the program representation of [filename] (if any)
      from the knowledge base. *)
  val load : string -> Program.t option

  (** [save filename] saves the program representation of [filename] to the
      knowledge base. *)
  val save : string -> Program.t -> unit

end

(** This module is used for interacting with the architecture for a binary. *)
module Arch : sig

  (** [load filename] obtains [filename]'s architecture from the knowledge base.
      This information is populated when BAP disassembles a binary, and does
      not need to be stored manually. *)
  val load : string -> Arch.t option

end
