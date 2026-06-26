module P = struct
  module I1 = Interval
  module I2 = Parity

  let reduce (i1, p) =
    (* complete the function *)
    if p == Parity.Top then (i1, p)
    else
      match i1 with
      | Interval.Inf n ->
          if p != Parity.of_int n then (Interval.Inf (n + 1), p) else (i1, p)
      | Interval.Minf n ->
          if p != Parity.of_int n then (Interval.Minf (n - 1), p) else (i1, p)
      | Interval.Range (x1, x2) ->
          ( Interval.Range
              ( (if p != Parity.of_int x1 then x1 + 1 else x1),
                if p != Parity.of_int x2 then x2 - 1 else x2 ),
            p )
      | _ -> (i1, p)
end

module Absint = Productint.Make (P)
module Absstring = Conststring
module Absarray = Squasharray.Make (Absint)
