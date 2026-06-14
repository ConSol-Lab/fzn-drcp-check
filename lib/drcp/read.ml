(* Whole contents of [file] as a string, transparently gunzipping a [.gz] path. *)
let slurp file =
  if Filename.check_suffix file ".gz" then (
    let ic = Gzip.open_in file in
    Fun.protect
      ~finally:(fun () -> Gzip.close_in ic)
      (fun () ->
        let buf = Buffer.create 0x10000 and chunk = Bytes.create 0x10000 in
        let rec go () =
          match Gzip.input ic chunk 0 (Bytes.length chunk) with
          | 0 -> ()
          | n ->
              Buffer.add_subbytes buf chunk 0 n;
              go ()
        in
        go ();
        Buffer.contents buf))
  else
    let ic = open_in_bin file in
    Fun.protect
      ~finally:(fun () -> close_in_noerr ic)
      (fun () -> really_input_string ic (in_channel_length ic))

let read_proof drcp_file = Parse.parse_proof (slurp drcp_file)

let read_binary_proof bin_file =
  Deserialize.deserialize_binary_proof (Bytes.unsafe_of_string (slurp bin_file))
