open Implementation
open Monolith

(** Reference implementation. *)
module R = ClosureSubst

(** Candidate implementation. *)
module C = SkewedSubst

let print_pair (d1 : PPrint.document) (d2 : PPrint.document) : PPrint.document =
  let open PPrint in
  let contents =
    [ string "("
    ; ifflat empty (blank 1)
    ; d1
    ; ifflat empty hardline
    ; string ", "
    ; d2
    ; ifflat empty (blank 1)
    ; string ")"
    ]
  in
  group @@ align @@ concat contents

let rec print_term (t : term) : PPrint.document =
  let open PPrint in
  match t with
  | Var i -> string ("Var " ^ string_of_int i)
  | App (t, u) ->
      group @@ align @@ string "App" ^^ print_pair (print_term t) (print_term u)
  | Lam t -> group @@ align @@ string "Lam" ^^ parens (print_term t)

let rec gen_term_fueled (n : int) : term =
  if n <= 0
  then Var (Gen.lt 16 ())
  else
    match Gen.le 2 () with
    | 0 -> Var (Gen.lt 16 ())
    | 1 -> App (gen_term_fueled (n - 1), gen_term_fueled (n - 1))
    | 2 -> Lam (gen_term_fueled (n - 1))
    | _ -> assert false

let gen_term : term Gen.gen =
 fun () ->
  let n = Gen.lt 16 () in
  gen_term_fueled n

let index : (int, int) spec = lt 16
let offset : (int, int) spec = lt 16

let term : (term, term) spec =
  ifpol (easily_constructible gen_term print_term) (deconstructible print_term)

let subst : (R.subst, C.subst) spec = declare_abstract_type ~var:"s" ()

(** Declare the operations. *)
let () =
  declare "apply" (subst ^> index ^> term) R.apply C.apply;
  declare "id" subst R.id C.id;
  declare "shift" (offset ^> subst) R.shift C.shift;
  declare "cons" (term ^> subst ^> subst) R.cons C.cons;
  declare "skip" (offset ^> subst ^> subst) R.skip C.skip;
  declare "up" (offset ^> subst ^> subst) R.up C.up

(** Run some tests. *)
let _ =
  run
    { source = Some "input/seed"
    ; timeout = Some 5.
    ; max_scenarios = 10
    ; show_scenario = true
    ; save_scenario = false
    ; prologue = (fun () -> ())
    ; fuel = 5
    }
