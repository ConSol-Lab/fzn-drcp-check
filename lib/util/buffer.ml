(** Buffer operations for efficient in-memory data management. *)

module DBuffer = struct
  type t = {
    data : bytes; (* The actual buffer data *)
    until : int; (* The index up to which the buffer contains valid data *)
    off : int; (* The current offset up to which data has been processed *)
  }

  (** [create size] creates a new empty buffer of [size] bytes *)
  let create size = { data = Bytes.create size; until = 0; off = 0 }

  (** [create_default] creates a new empty buffer. *)
  let create_default () = create 4096

  (** [resize buf new_len] resizes the buffer [buf] to [new_len] bytes and
      copies unprocessed data to the beginning of the new buffer *)
  let resize buf new_len =
    let new_data = Bytes.create new_len in
    let rem_len = buf.until - buf.off in

    (* Ensure the new buffer can hold the remaining data *)
    assert (rem_len <= new_len);

    Bytes.blit buf.data buf.off new_data 0 rem_len;
    { data = new_data; until = rem_len; off = 0 }

  (** [shift buf] clears processed data from the buffer [buf] and shifts
      remaining data to the beginning *)
  let shift buf =
    let rem_len = buf.until - buf.off in
    Bytes.blit buf.data buf.off buf.data 0 rem_len;
    { data = buf.data; until = rem_len; off = 0 }

  (** [data buf] returns the underlying byte array of the buffer [buf] for
      reading and writing *)
  let data buf = buf.data

  (** [length buf] returns the total length of the buffer [buf] *)
  let length buf = Bytes.length buf.data

  (** [can_read buf len] returns [true] if [len] bytes can be read from the
      buffer [buf] and [false] if not. *)
  let can_read buf len = buf.until - buf.off >= len

  (** [fill buf fd len] reads [len] bytes from file descriptor [fd] into buffer
      [buf], starting from [buf.until]. Updates [buf.until] to how many bytes
      were actually read*)
  let fill buf fd =
    let bytes_read = Unix.read fd buf.data buf.until (length buf - buf.until) in
    if bytes_read = 0 then (
      Unix.close fd;
      failwith "Unexpected end of buffer");
    { data = buf.data; until = buf.until + bytes_read; off = buf.off }

  (** round up [len] to nearest multiple of [bufsz = 4096] *)
  let compute_bufsz len =
    let bufsz = 0x1000 in
    (len + bufsz - 1) / bufsz * bufsz

  (** [read_if_unavailable fd buf until off len] checks if [len] bytes can still
      be read from the buffer and fills the buffer with more data from [fd] if
      [off + len] is larger than [until]. If [len] is greater than [bufsz], the
      underlying buffer is resized to the nearest page. Returns a new buffer
      positioned at the offset from which to read. *)
  let rec read_if_unavailable fd (buf : t) len : t =
    let bufsz = length buf in

    if len > bufsz then
      (* resize buf to fit requested length *)
      let new_bufsz = compute_bufsz len in

      (* copy existing data *)
      let new_buf = resize buf new_bufsz in
      let new_buf = fill new_buf fd in

      read_if_unavailable fd new_buf len
    else if Bool.not (can_read buf len) then
      (* move data to start of buffer if not enough is left *)
      let new_buf = if buf.until >= bufsz then shift buf else buf in
      let new_buf = fill new_buf fd in

      read_if_unavailable fd new_buf len
    else buf
end
