(** Implements {!Help}. *)

open Core_kernel
open Bap_primus.Std

module Make (Machine : Primus.Machine.S) = struct
  module Event = Ui.Event (Machine)

  type event = Event.t

  (** Generates a screen that displays the help menu. *)
  let menu ?prompt:(prompt=None) ?handler:(handler=None) () : event Machine.t =
    let data = [
      "At the prompt, type any of the following commands.";
      "";
      "COMMAND        PURPOSE";
      "h              Show this help";
      "q              Quit";
      "s or -s        Step to the next/previous instruction";
      "n or -n        Continue to the next/previous breakpoint or block";
      "show N         Show +/- N surrounding instructions (e.g., show 3)";
      "always show N  Always show +/- N surrounding instructions"; 
      "b %tid         Set a breakpoint at %tid (e.g., b %00000df1)";
      "clear %tid     Clear a breakpoint at %tid (e.g., clear %00000df1)";
      "breaks         Print the list of breakpoints";
      "all            Print values of all variables in environment";
      "regs           Print values of all registers";
      "p REG          Print value of REG (e.g., p RAX)";
      "p ADDR         Print byte stored at ADDR (e.g., p 0x4000000)";
      "p ADDR N       Print N bytes starting at ADDR (e.g., p 0x3ffffff0 16)";
      "set REG=VAL    Set REG to hex VAL (e.g., set RAX=0x00000abc)";
      "set ADDR=VAL   Set ADDR to hex VAL byte (e.g., set 0x3ffffff1=0x3f)";
      "[enter]        Hitting the enter key repeats your last command"; 
      ] in
    let text = List.map data ~f:(fun s -> Ui.mk_output s) in
    Machine.return (Event.screen () ~text ~prompt ~handler)

end
