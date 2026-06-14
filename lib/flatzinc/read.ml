let read_constraint_problem flatzinc_file =
  In_channel.with_open_text flatzinc_file (fun channel ->
      let lexbuf = Lexing.from_channel channel in
      Parse.parse lexbuf (Some flatzinc_file))
