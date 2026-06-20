type t = { data : Bigstringaf.t; off : int (* consumed up to here *); until : int (* filled up to here *) }

let create n = { data = Bigstringaf.create (Stdlib.max n 4096); off = 0; until = 0 }

(* Make room, then read one chunk via [read] into [w.data] through [staging].  Returns [true] at EOF. *)
let refill read staging w =
  let cap = Bigstringaf.length w.data in
  let w =
    if w.until < cap then w
    else if w.off > 0 then
      let len = w.until - w.off in
      Bigstringaf.blit w.data ~src_off:w.off w.data ~dst_off:0 ~len;
      { w with off = 0; until = len }
    else
      let data = Bigstringaf.create (2 * cap) in
      Bigstringaf.blit w.data ~src_off:0 data ~dst_off:0 ~len:w.until;
      { w with data }
  in
  let room = Bigstringaf.length w.data - w.until in
  match read staging 0 (Stdlib.min (Bytes.length staging) room) with
  | 0 -> (w, true)
  | n ->
      Bigstringaf.blit_from_bytes staging ~src_off:0 w.data ~dst_off:w.until ~len:n;
      ({ w with until = w.until + n }, false)

(* Parse one value with [p] out of the window, refilling via [read] as the parser asks. *)
let parse_one read staging p w : ('a, string) result * t =
  let open Angstrom.Unbuffered in
  let rec drive st w =
    match st with
    | Done (consumed, res) -> (Ok res, { w with off = w.off + consumed })
    | Fail (_, _, msg) -> (Error msg, w)
    | Partial { committed; continue } ->
        let w = { w with off = w.off + committed } in
        let w, eof = refill read staging w in
        let more = if eof then Complete else Incomplete in
        drive (continue w.data ~off:w.off ~len:(w.until - w.off) more) w
  in
  match parse p with
  | Partial { continue; _ } ->
      drive (continue w.data ~off:w.off ~len:(w.until - w.off) Incomplete) w
  | st -> drive st w
