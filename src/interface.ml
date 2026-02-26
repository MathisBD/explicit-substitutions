(** Untyped lambda calculus terms, using de Bruijn indices. *)
type term =
  | Var of int  (** De Bruijn index. *)
  | App of term * term  (** Application. *)
  | Lam of term  (** Lambda abstraction. *)

module type ESubst = sig
  (** The type of substitutions, i.e. functions from indices to terms. If [s] is a
      substitution, we write [s i] for the application of [s] to an index [i : int], and
      [s t] for the application of [s] to a term [t : term].

      Substitutions are in fact _finite_ functions: we write [s : n --> m] to indicate
      that [s] maps indices in the range [0..n-1] to terms which have free indices in the
      range [0..m-1]. *)
  type subst

  (** [apply s i] applies the substitution [s : n --> m] to the index [i]. Assumes [i] is
      in the range [0..n-1]. *)
  val apply : subst -> int -> term

  (** [id : n --> n] is the identity substitution on [n] variables, which maps [i] to
      [Var i]. *)
  val id : subst

  (** [shift k : n --> n + k] is the substitution on [n] variables which shifts every
      index by [k]: it maps [i] to [Var (i + k)]. *)
  val shift : int -> subst

  (** Given a substitution [s : n --> m] and a term [t], [cons t s : n + 1 --> m] is a
      substitution which maps [0] to [t] and [i + 1] to [s i]. *)
  val cons : term -> subst -> subst

  (** Given a substitution [s : n --> m], [skip k s : n --> m + k] is the composition of
      [s] followed by [shift k]. *)
  val skip : int -> subst -> subst

  (** Given a substitution [s : n --> m], [up k s : n + k --> m + k] is a substitution
      which lifts [s] under [k] binders. It maps:
      - [i] to [i] if [i < k].
      - [i] to [weaken k (s (i - k))] if [i >= k]. *)
  val up : int -> subst -> subst
end

(** This module showcases an example use-case for substitutions: implementing beta
    reductions. Substitutions are used pervasively when manipulating lambda terms.

    Unfortunately we need to use an OCaml functor here, hopefully modular explicits will
    solve this issue in the future. *)
module Substitute (S : ESubst) = struct
  (** [substitute s t] applies the substitution [s] to a term [t]. *)
  let rec substitute (s : S.subst) (t : term) : term =
    match t with
    | Var i -> S.apply s i
    | App (t, u) -> App (substitute s t, substitute s u)
    | Lam t -> Lam (substitute (S.up 1 s) t)

  (** [reduce t] applies weak head beta-reduction to the term [t]. *)
  let rec reduce (t : term) : term =
    match t with
    | App (t, u) -> begin
        match reduce t with
        | Lam body -> reduce (substitute (S.cons u S.id) body)
        | _ -> App (t, u)
      end
    | _ -> t
end

(** [weaken_rec depth ofs t] adds [ofs] to every index greater or equal to [depth] in [t].
*)
let rec weaken_rec (depth : int) (ofs : int) (t : term) : term =
  match t with
  | Var i -> if i < depth then Var i else Var (i + ofs)
  | App (t, u) -> App (weaken_rec depth ofs t, weaken_rec depth ofs u)
  | Lam t -> Lam (weaken_rec (depth + 1) ofs t)

(** [weaken ofs t] adds [ofs] to every index in [t]. *)
let weaken (ofs : int) (t : term) : term = weaken_rec 0 ofs t

module ClosureSubst : ESubst = struct
  type subst = int -> term

  let apply s i : term = s i
  let id : subst = fun i -> Var i
  let shift k : subst = fun i -> Var (i + k)
  let cons t s : subst = fun i -> if i = 0 then t else s (i - 1)
  let up k s : subst = fun i -> if i < k then Var i else weaken k (s (i - k))
  let skip k s : subst = fun i -> weaken k (s i)
end

(** [range n] builds the list [0; 1; ...; n-1]. *)
let range (n : int) : int list =
  let rec loop i acc = if i <= 0 then acc else loop (i - 1) ((i - 1) :: acc) in
  loop n []

(** With this implementation:
    - [apply] is O(n).
    - [id], [shift], [cons], [skip] are O(1).
    - [up k] is O(k).

    So basically building a substitution is cheap but applying it is expensive. *)
module ListSubst : ESubst = struct
  (** We encode a substitution as a list of terms followed by shifts.
      - [Nil k] represents the substitution [shift k]. In particular [Nil 0] is the
        identity.
      - [Cons k t s] represents the substitution [skip k (cons t s)]; it maps [0] to
        [weaken k t] and [i + 1] to [weaken k (s i)]. *)
  type subst = Nil of int | Cons of int * term * subst

  let rec apply_rec (acc : int) s i : term =
    match s with
    | Nil k -> Var (i + k + acc)
    | Cons (k, t, s) -> if i = 0 then weaken (k + acc) t else apply_rec (k + acc) s (i - 1)

  let apply s i : term = apply_rec 0 s i
  let id : subst = Nil 0
  let shift k : subst = Nil k
  let cons t s : subst = Cons (0, t, s)

  let skip k0 s : subst =
    match s with Nil k -> Nil (k0 + k) | Cons (k, t, s) -> Cons (k0 + k, t, s)

  let rec cons_vars (n : int) (s : subst) : subst =
    if n <= 0 then s else cons_vars (n - 1) (Cons (0, Var (n - 1), s))

  let up k0 s : subst = cons_vars k0 (skip k0 s)
end

module SkewedSubst = struct
  type tree =
    | Leaf of { k : int; t : term }
        (** [Leaf k t] represents the substitution [skip k (cons t id)]. *)
    | Node of { k : int; k_tot : int; t : term; left : tree; right : tree }
        (** [Node (k, k_tot, t, s1, s2, )] represents the substitution
            [skip k (cons t (app s1 s2))] where [app] is the n-ary version of [cons] and
            is defined as you would expect.

            [k_tot] is equal to the total shift stored in the tree, which can be defined
            as follows:
            {[
              total_shift (Leaf (k, _)) = k
            ]}
            {[
              total_shift (Node (k, t, s1, s2, _)) = k + total_shift s1 + total_shift s2
            ]}
            The purpose of [k_tot] is purely to avoid recomputing [total_shift] all the
            time when applying a substitution to an index. *)

  (** We encode a substitution as a spine of trees.
      - [Nil k] represents the substitution [shift k]. In particular [Nil 0] is the
        identity.
      - [Cons n t s] represents the substitution [cons t s], where [t] is a complete
        binary tree of size [n]. Thus [n] is equal to [2^h - 1] where [h] is the height of
        [t]. Note that a [Cons] node doesn't need to contain a shift, because the tree
        itself [t] can contain shifts.

      Additionally, we maintain the invariant that the spine of a substitution contains
      trees of (non-strictly) increasing height, and at most the first two trees have the
      same height. This invariant ensures that the length of the spine of the substitution
      is logarithmic in the number of terms in the substitution. *)
  type subst = Nil of int | Cons of int * tree * subst

  (** [total_shift tr] returns the value of the total shift stored in the tree [tr].
      Thanks to the use of [k_tot] this function is O(1). *)
  let total_shift (tr : tree) : int =
    match tr with Leaf { k } -> k | Node { k_tot } -> k_tot

  (** [leaf t] builds a leaf with a shift [k = 0]. *)
  let leaf (t : term) : tree = Leaf { k = 0; t }

  (** [node t left right] builds a leaf with a shift [k = 0]. *)
  let node (t : term) (left : tree) (right : tree) : tree =
    Node { k = 0; k_tot = total_shift left + total_shift right; t; left; right }

  let rec apply_tree (acc : int) (n : int) (tr : tree) (i : int) : term =
    match tr with
    | Leaf { k; t } -> weaken (acc + k) t
    | Node { k; t; left; right } ->
        if i = 0
        then weaken (acc + k) t
        else if i <= n / 2
        then apply_tree (acc + k) (n / 2) left (i - 1)
        else apply_tree (acc + k + total_shift left) (n / 2) right (i - 1 - (n / 2))

  let rec apply_rec (acc : int) s i : term =
    match s with
    | Nil k -> Var (i + k + acc)
    | Cons (n, t, s) ->
        if i < n then apply_tree acc n t i else apply_rec (acc + total_shift t) s (i - n)

  let apply s i : term = apply_rec 0 s i
  let id : subst = Nil 0
  let shift k : subst = Nil k

  let cons (t : term) (s : subst) : subst =
    match s with
    | Cons (n1, tr1, Cons (n2, tr2, tail)) when n1 = n2 ->
        Cons (1 + n1 + n2, node t tr1 tr2, tail)
    | _ -> Cons (1, leaf t, s)

  let skip_tree k0 (tr : tree) : tree =
    match tr with
    | Leaf { k; t } -> Leaf { k = k + k0; t }
    | Node { k; k_tot; t; left; right } ->
        Node { k = k + k0; k_tot = k_tot + k0; t; left; right }

  let skip k0 s : subst =
    match s with Nil k -> Nil (k0 + k) | Cons (n, t, s) -> Cons (n, skip_tree k0 t, s)

  let rec cons_vars (n : int) (s : subst) : subst =
    if n <= 0 then s else cons_vars (n - 1) (cons (Var (n - 1)) s)

  let up k0 s : subst = cons_vars k0 (skip k0 s)
end
