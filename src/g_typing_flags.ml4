DECLARE PLUGIN "typing_flags_plugin"


VERNAC COMMAND EXTEND TypingFlags1 CLASSIFIED AS SIDEFF
| [ "Unset" "Guard" "Checking" ] -> [ Typing_flags_main.set_check_guarded false ]
END

VERNAC COMMAND EXTEND TypingFlags2 CLASSIFIED AS SIDEFF
| [ "Set" "Guard" "Checking" ] -> [ Typing_flags_main.set_check_guarded true ]
END

VERNAC COMMAND EXTEND TypingFlags3 CLASSIFIED AS SIDEFF
| [ "Set" "Type" "In" "Type" ] -> [ Typing_flags_main.set_check_universes false ]
END

VERNAC COMMAND EXTEND TypingFlags4 CLASSIFIED AS SIDEFF
| [ "Unset" "Type" "In" "Type" ] -> [ Typing_flags_main.set_check_universes true ]
END

VERNAC COMMAND EXTEND TypingFlags5 CLASSIFIED AS QUERY
| [ "Print" "Typing" "Flags" ] -> [ Typing_flags_main.print_typing_flags () ]
END
