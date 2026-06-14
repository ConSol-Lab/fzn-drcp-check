let read_proof drcp_file =
  let proof_handle = open_in drcp_file in
  let source =
    really_input_string proof_handle (in_channel_length proof_handle)
  in
  close_in proof_handle;
  Parse.parse_proof source

let read_binary_proof bin_file =
  let chan = open_in_bin bin_file in
  let len = in_channel_length chan in
  let source = Bytes.create len in
  really_input chan source 0 len;
  close_in chan;
  Deserialize.deserialize_binary_proof source
