type itv = int * int

let print_itv fmt (low, sup) =
  if low = sup then Format.fprintf fmt "%i" sup
  else Format.fprintf fmt "[%i;%i]" low sup

type t =
  | Range of itv
  | Minf of int  (** [Minf(up)] is the set of values [x | x <= up] *)
  | Inf of int  (** [Inf(low)] is the set of values [x | x >= low] *)
  | Top

let print fmt itv =
  match itv with
  | Top -> Format.fprintf fmt "]-oo;+oo["
  | Minf u -> Format.fprintf fmt "]-oo;%i]" u
  | Inf l -> Format.fprintf fmt "[%i;+oo[" l
  | Range itv -> print_itv fmt itv

(* join *)
(* Step 4 *)
let join i1 i2 =
  match (i1, i2) with
  | Range (l1, l2), Range (r1, r2) -> Range (min l1 r1, max l2 r2)
  | Range (_, n), Minf high | Minf high, Range (_, n) -> Minf (max n high)
  | Range (n, _), Inf low | Inf low, Range (_, n) -> Inf (min n low)
  | _ -> Top

let widen _ _ = Top

let subset a b =
  match (a, b) with
  | _, Top -> true
  | Range (l1, h1), Range (l2, h2) -> l2 <= l1 && h1 <= h2
  | Range (_, u), Minf u' | Minf u, Minf u' -> u <= u'
  | Range (l, _), Inf l' | Inf l, Inf l' -> l >= l'
  | _ -> false

(* arith*)

(** negation of an interval *)
let neg (i : t) : t =
  match i with
  | Top -> Top
  | Inf x -> Minf (-x)
  | Minf x -> Inf (-x)
  | Range (l, u) -> Range (-u, -l)

(* Step 4 *)
let add i1 i2 =
  match (i1, i2) with
  | Range (r1, r2), Range (l1, l2) -> Range (l1 + r1, l2 + r2)
  | Range (_, n), Minf high | Minf high, Range (_, n) -> Minf (n + high)
  | Range (n, _), Inf low | Inf low, Range (_, n) -> Inf (n + low)
  | _ -> Top

let sub i1 i2 =
  match (i1, i2) with
  | Range (x1, x2), Range (y1, y2) -> Range (x1 - y2, x2 - y1)
  | Range (x1, _), Minf y2 -> Inf (x1 - y2)
  | Minf x2, Range (y1, _) -> Minf (x2 - y1)
  | Range (_, x2), Inf y1 -> Minf (x2 - y1)
  | Inf x1, Range (_, y2) -> Inf (x1 - y2)
  | _ -> Top

let mul i1 i2 =
  match (i1, i2) with
  | Range (x1, x2), Range (y1, y2) ->
      Range
        ( List.fold_left min (x1 * y1) [ x1 * y2; x2 * y1; x2 * y2 ],
          List.fold_left max (x1 * y1) [ x1 * y2; x2 * y1; x2 * y2 ] )
  | _, _ -> Top

let div _i1 _i2 = Top

(* truth handling *)
let false_ = Range (0, 0)
let true_ = Range (1, 1)
let maybe_ = Range (0, 1)

let truth = function
  | Range (0, 0) -> Domain.False
  | Range (1, 1) -> Domain.True
  | _ -> Domain.Unknown

let bool_to_Bool (b : bool) = if b then true_ else false_

(* boolean logic *)
(* Tiger Boolean operators normalize their result to 0 or 1 *)
let logical_and a b =
  if subset a false_ || subset b false_ then false_ else maybe_

let logical_or a b =
  if subset a false_ && subset b false_ then false_ else maybe_

(* comparisons *)
(* Step 4 *)
let eq i1 i2 =
  bool_to_Bool
    (match (i1, i2) with
    | Range (x1, x2), Range (y1, y2) -> x1 == y1 && x2 == y2
    | Inf x1, Inf y1 -> x1 == y1
    | Minf x2, Minf y2 -> x2 == y2
    | Top, Top -> true
    | _, _ -> false)

let ne i1 i2 = if eq i1 i2 == true_ then false_ else true_

let gt i1 i2 =
  match (i1, i2) with
  | Range (x1, x2), Range (y1, y2) ->
      if x1 > y2 then true_ else if x2 <= y1 then false_ else maybe_
  | Range (x1, _), Minf y2 -> if x1 > y2 then true_ else maybe_
  | Minf x2, Range (y1, _) -> if x2 < y1 then false_ else maybe_
  | Range (_, x2), Inf y1 -> if x2 <= y1 then false_ else maybe_
  | Inf x2, Range (_, y2) -> if x2 <= y2 then maybe_ else false_
  | Minf x2, Inf y1 -> if x2 <= y1 then false_ else maybe_
  | Inf x1, Minf y2 -> if x1 > y2 then true_ else maybe_
  | _ -> maybe_

let ge i1 i2 =
  match (i1, i2) with
  | Range (x1, x2), Range (y1, y2) ->
      if x1 >= y2 then true_ else if x2 < y1 then false_ else maybe_
  | Range (x1, _), Minf y2 -> if x1 >= y2 then true_ else maybe_
  | Minf x2, Range (y1, _) -> if x2 <= y1 then false_ else maybe_
  | Range (_, x2), Inf y1 -> if x2 < y1 then false_ else maybe_
  | Inf x2, Range (_, y2) -> if x2 < y2 then maybe_ else false_
  | Minf x2, Inf y1 -> if x2 < y1 then false_ else maybe_
  | Inf x1, Minf y2 -> if x1 >= y2 then true_ else maybe_
  | _ -> maybe_

let lt i1 i2 =
  match (i1, i2) with
  | Range (x1, x2), Range (y1, y2) ->
      if x1 >= y2 then false_ else if x2 < y1 then true_ else maybe_
  | Range (x1, _), Minf y2 -> if x1 >= y2 then false_ else maybe_
  | Minf x2, Range (y1, _) -> if x2 <= y1 then true_ else maybe_
  | Range (_, x2), Inf y1 -> if x2 < y1 then true_ else maybe_
  | Inf x2, Range (_, y2) -> if x2 < y2 then maybe_ else true_
  | Minf x2, Inf y1 -> if x2 < y1 then true_ else maybe_
  | Inf x1, Minf y2 -> if x1 >= y2 then false_ else maybe_
  | _ -> maybe_

let le i1 i2 =
  match (i1, i2) with
  | Range (x1, x2), Range (y1, y2) ->
      if x1 > y2 then false_ else if x2 <= y1 then true_ else maybe_
  | Range (x1, _), Minf y2 -> if x1 > y2 then false_ else maybe_
  | Minf x2, Range (y1, _) -> if x2 < y1 then true_ else maybe_
  | Range (_, x2), Inf y1 -> if x2 <= y1 then true_ else maybe_
  | Inf x2, Range (_, y2) -> if x2 <= y2 then maybe_ else true_
  | Minf x2, Inf y1 -> if x2 <= y1 then true_ else maybe_
  | Inf x1, Minf y2 -> if x1 > y2 then false_ else maybe_
  | _ -> maybe_

(* constructors *)
let of_int x = Range (x, x)
let range l h = join l h

(* Ensure the interval is non-empty.  If the interval is invalid
   (upper bound less than lower bound), raise Domain.Bot_found to signal
   inconsistency. *)
let validate = function
  | Range (l, h) when h < l -> raise Domain.Bot_found
  | itv -> itv

(* comparisons *)

(* Interval refinement functions for relational constraints.
   Given two intervals, these functions compute a refined interval for the first operand
   that satisfies the given comparison against the second operand.
   - Each function returns a possibly narrowed interval, or raises Domain.Bot_found if the result is empty.
   - Intervals should be validated to ensure they are non-empty after refinement.

   hint: try first to implement the easy case when comparing two
   ranges and default to returning i1 in the other cases as shown
   here:
*)
let filter_eq i1 i2 =
  match (i1, i2) with
  | Range (l1, h1), Range (l2, h2) ->
      let l = max l1 l2 in
      let h = min h1 h2 in
      Range (l, h) |> validate
  | _ -> i1

let filter_ne i1 i2 =
  match (i1, i2) with
  | Range _, Range _ -> Top
  | _ -> i1

let filter_gt i1 i2 =
  match (i1, i2) with
  | _ -> i1

let filter_ge i1 i2 =
  match (i1, i2) with
  | _ -> i1

let filter_lt i1 i2 =
  match (i1, i2) with
  | _ -> i1

let filter_le i1 i2 =
  match (i1, i2) with
  | _ -> i1
