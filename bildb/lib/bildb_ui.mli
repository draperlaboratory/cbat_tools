(** Handles the rendering of the user interface.

    The UI is implemented here as a stream of {!Event.t} events
    that occur one after the other in a terminal. Basically, events
    are screens, which are rendered one after the other, until a 
    "finished" event occurs (which ends the sequence), or a "quit" event
    occurs (which exits the program altogether). 

    Screens can ask the user for input, and then return a new event, which
    can be a quit event, a finished event, or a new screen.

    To create events, use the constructors in the {!Event} module.
    To render events, use the {!Make.render} function. *)

open Core_kernel
open Bap_primus.Std

module Tty = Bildb_tty

(** This type represents user input. *)
type input

(** This type represents output to print to the UI (terminal). *)
type output

(** This function converts a string into user input. *)
val mk_input : string -> input

(** This function constructs output that can be printed to the UI (terminal).
    For example, [mk_output ~style:Tty.Red "Hello"] builds the line "hello,"
    which will be red when printed to the terminal. *)
val mk_output : ?style:Tty.style -> ?color:Tty.color -> ?newline:string -> 
  string -> output

(** Gets the string value of a line of {!output}. *)
val string_of_output : output -> string

(** Gets the string value of a line of user {!input}. *)
val string_of_input : input -> string

(** Min width to print a key/identifier. *)
val key_width : int

(** Padding between columns printed to terminal. *)
val col_padding : int

(** Max width of terminal screen. *)
val screen_width : int

(** This module represents UI events. A UI {!Event.t} can be any of these:
    - Quit: Represents quitting the UI.
    - Finished: Like EOF, it represents the end of a stream of events.
    - Screen: Represents a screen that can be drawn to the UI (terminal).

    Screens can include any of these three components:
    - Text: A list of {!output} lines to print to the screen.
    - Prompt: A prompt (some {!output}) that asks the user for input.
    - Handler: A function that takes user {!input}, and returns
      a new UI {Event.t}.

    Each kind of {Event.t} has a constructor: see {!quit}, {!finished},
    and {!screen}. 

    Note that this module does not render UI events. Rather, it merely
    encodes the information that defines such events.

    To render a UI {Event.t}, use the {!Make.render} function below. *)
module Event : functor (Machine : Primus.Machine.S) -> sig

  (** This type represents a UI event. *)
  type t

  (** Constructs a "Quit" UI event. *)
  val quit : unit -> t

  (** Constructs a "Finished" UI event. *)
  val finished : unit -> t

  (** Constructs a "Screen" UI event. A screen can have some text to print
      to the UI (terminal), it can include a prompt/cue to ask the user 
      for input, and it can have a handler function which takes the user's
      input and, after processing it, returns a new {Event.t} (but
      wrapped in a Primus Machine, so {Event.t Machine.t}). *)
  val screen : ?text:output list -> ?prompt:output option ->
    ?handler:(input -> t Machine.t) option -> unit -> t

end

(** This module renders a UI {Event.t}. 

    Depending on the type of event, the {!Make.render} function does this:
    - If it's a "Quit" event, this function will exit the program.
    - If it's a "Finished" event, this function does nothing (it ends).
    - If it's a "Screen" event, this function renders the screen,
      and then it renders whatever new event the screen returns.

    Note that screens can include text, a prompt, and a handler:
    - If there's text to print, the text will be printed to the UI.
    - If there's a prompt, the cue will be printed and the user
      will be asked for input.
    - If there's a handler, the user's input will be gathered from STDIN,
      and passed to the handler, which can process that input however it
      sees fit. The handler will then return a new {!Event.t} (but wrapped
      in a Primus Machine, so {Event.t Machine.t}), which the {!Make.render}
      function will proceed to render.

    If a screen includes no prompt or handler, it simply returns 
    a "Finished" event after it is rendered.

    The {!Make.render} function is recursive, so if it renders a screen
    with a handler that returns a new screen, it will render that new
    screen too, and the process can repeat until a quit or finish event
    is encountered. *)
module Make : functor (Machine : Primus.Machine.S) -> sig
  type event = Event (Machine).t

  (** See the description above for details. *)
  val render : event  -> event Machine.t

end
