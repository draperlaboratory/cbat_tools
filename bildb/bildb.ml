(** The main entry point into the plugin. *)

open Core_kernel
open Bap.Std
open Bap_primus.Std
include Self ()

module Init = Bildb_init
module Startup = Bildb_startup
module Position = Bildb_position

module Param = struct
  open Config

  let () = manpage [
      `S "DESCRIPTION";
      `P "A Primus-based BIL debugger.";
    ]

  let debug = flag "debug" ~doc:"Run the debugger."
  let init_file = param string "init" ~doc:"/path/to/file.yml"

end

(* A helper function to load/parse an init-file if one is specified. *)
let load_state filepath =
  match String.is_empty filepath with
  | true -> None
  | false ->
    begin
      match Init.from_file filepath with
      | Ok state -> Some state
      | Error e -> Printf.printf "%s\n%!" e; exit 1
    end

let main {Config.get=(!)} =

  (* We only want to proceed if the user specified the [debug] flag. *)
  match !Param.debug with
  | false -> ()
  | true ->
    begin

      (* Load any initial state from an init file. *)
      let module Config : Startup.Configuration = struct
        let initial_state = load_state !Param.init_file
      end in

      (* Register the component that initializes things. *)
      let module Startup = Startup.Make (Config) in
      Primus.Machine.add_component (module Startup) [@warning "-D"];

      (* Register the component that triggers the debugger. *)
      Primus.Machine.add_component (module Position.Make) [@warning "-D"];

    end

let () = Config.when_ready main
