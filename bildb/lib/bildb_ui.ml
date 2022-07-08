(** Implements {!Ui}. *)

open Core
open Bap_primus.Std

module Tty = Bildb_tty

type input = string
type output = Tty.t

let mk_input (s : string) : input = s

let mk_output ?style:(style=Tty.Plain) ?color:(color=Tty.Default) 
    ?newline:(newline="") (s : string) : output = 
  Tty.mk s ~style ~color ~newline

let string_of_output (s : output) : string = Tty.to_string s
let string_of_input (s : input) : string = s

let key_width = 6
let col_padding = 2
let screen_width = 80

module Event (Machine : Primus.Machine.S) = struct

  type t =
    | Quit
    | Finished
    | Screen of {
        text : output list;
        prompt : output option; 
        handler : (input -> t Machine.t) option;
      }

  let quit () : t = Quit
  let finished () : t = Finished

  let screen ?text:(text=[]) ?prompt:(prompt=None) ?handler:(handler=None)
      () : t =
    Screen { text; prompt; handler; }

end

module Make (Machine : Primus.Machine.S) = struct
  module Event = Event (Machine)
  open Machine.Let_syntax
  let (let*) = (>>=)

  type event = Event.t

  let read () =
    let raw = Stdio.In_channel.(input_line_exn stdin) in
    String.strip raw

  let render_text (text : output list) : unit =
    List.iter text ~f:(fun s -> print_endline (Tty.for_terminal s))

  let render_prompt (cue : output) : unit =
    Printf.printf ">>> %s %!" (Tty.for_terminal cue)

  let rec render (event : event) : event Machine.t =
    match event with
    | Event.Quit -> print_endline "Goodbye"; exit 1
    | Event.Finished -> Machine.return Event.Finished
    | Event.Screen { text; prompt; handler; } -> 
      begin
        let () = render_text text in
        match prompt with
        | None -> Machine.return Event.Finished
        | Some cue ->
          begin
            let () = render_prompt cue in
            let user_input = read () in
            match handler with
            | None -> Machine.return Event.Finished
            | Some f ->
              begin
                let* result = f user_input in
                render result
              end
          end
      end

end
