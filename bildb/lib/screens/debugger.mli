(** This module has the main debug loop handler.

    This handler processes the debugger commands that users type in.
    For example, it checks if the user typed [h] (to display the help),
    [q] (to quit), [s] (to step to the next instruction), and so on,
    and then it returns the appropriate screen/UI event accordingly.

    This handler is usually triggered by other screens, which display
    some information, and then prompt the user to enter a debugger command.
    
    See the {!Ui} module for more about screens and user input handlers. *)

open Bap_primus.Std

module Make : functor (Machine : Primus.Machine.S) -> sig
  type event = Ui.Event (Machine).t

  (** [main_loop user_input] will handle the user input, and return
      the appropriate next screen/UI event. For instance, if the user
      input is [q], this function will return a "quit" UI event (see
      {!Ui.Event}. If the user input is [h], this function will 
      trigger the help screen. *)
  val main_loop : Ui.input -> event Machine.t

end
