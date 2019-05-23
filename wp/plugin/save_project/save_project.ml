open !Core_kernel
open Bap.Std
include Self()


let main nm proj : unit =
  let dest = 
    match (nm, Project.get proj filename) with
    | ("",None) -> printf "Please specify a destination filename with --save-project-filename.\n";
                   exit 1;
    | ("",Some bnm) -> String.concat [bnm;".bpj"]
    | (user_dest,_) -> user_dest
  in
  Project.Io.write dest proj

module Cmdline = struct
  open Config
  let filename = param string "filename" ~doc:"Optional name of output file"
                 
  let () = when_ready (fun {get=(!!)} ->
               Project.register_pass' (main !!filename))
             
  let () = manpage [
     `S "DESCRIPTION";
     `P "Saves a binary's project data structure to disk."
  ]
end
