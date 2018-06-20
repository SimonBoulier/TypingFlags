open Declarations
open Environ
open Pp

let set_check_guarded b =
  let env = Global.env () in
  let flags = {(typing_flags env) with check_guarded = b} in
  Global.set_typing_flags flags

let print_typing_flags () =
  let flags = typing_flags (Global.env ()) in
  Feedback.msg_notice (str "check_guarded: " ++ bool flags.check_guarded
                      ++ str "\ncheck_universes: " ++ bool flags.check_universes)

let set_check_universes b =
  let env = Global.env () in
  let flags = {(typing_flags env) with check_universes = b} in
  Global.set_typing_flags flags
