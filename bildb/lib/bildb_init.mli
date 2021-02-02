(** This module loads initial state information from a file. 

    In particular, this module loads a file that looks like this:

    {[
      Variables:
        RAX: 0x00000abc
          RDI: 0xdeadbeaf
          Locations:
        0x3ffffff1: 0x00000003
    ]}

    It parses that file, and builds a {!Data.State.t} record, to
    hold this information, which it returns. *)

open Core_kernel

module State = Bildb_state

(** [from_file "/path/to/init.yml"] loads and parses the info in the
    specified file, and tries to build a {!State.Data.t} record of it.
    If it succeeds, it returns an [Ok] result. If it fails, it returns
    an [Error] string with information about what is wrong. *)
val from_file : string -> (State.Data.t, string) Stdlib.result
