# Three implementations of explicit substitutions

## Lambda terms

Consider the standard (untyped) lambda calculus, which consists of variables, applications, and lambda abstractions:
```
t ::= x            (variable)
    | t u          (application)
    | fun x => t   (lambda abstraction)
```

To encode lambda terms in OCaml one has to choose a representation for variables. Using strings is not a good idea, for reasons we will not dive into here. A popular option is to use de Bruijn indices: a variable occurence is represented by an integer `i >= 0` which refers to the `i`-th binder counting upwards:
```ocaml
type term =
  | Var of int
  | App of term * term
  | Lam of term
```
De Bruijn indices are notably found in the implementations of modern theorem provers (e.g. Rocq, Agda, Lean).

Some example lambda terms:
- The identity function `fun x => x` encoded as `Lam (Var 0)`.
- The first projection `fun x y => x` encoded as `Lam (Lam (Var 1))`.
- The second projection `fun x y => y` encoded as `Lam (Lam (Var 0))`.

TODO: closed vs open terms?

## Parallel substitution

A pervasive operation on lambda terms is _parallel substitution_, which replaces some or all of the free variables in a term with new terms. Because of the many quirks of de Bruijn indices, this is actually quite tricky to implement efficiently. The remainder of this blog post gently builds up to an efficient implementation.

Let us first consider a simple but inefficient implementation of substitution. Given a term `t : term` and a substitution `s : int -> term` which maps indices to terms, we can substitute with `s` in `t` as follows:
```ocaml
let rec substitute (s : int -> term) (t : term) : term =
  match t with
  | Var i -> s i
  | App (t, u) -> App (substitute s t, substitute s u)
  | Lam t -> Lam (substitute (up s) t)
```
Notice that in the `Lam` case we need to modify the substitution `s` so as take into account the new variable with index `0` which should be left unchanged. Formally, `up s` is defined as:
```ocaml
let up (s : int -> term) : int -> term =
  fun i -> if i = 0 then Var 0 else weaken (s (i - 1))
```
where `weaken t` increments every free index in `t`.

## Explicit substitution interface

We wish to implement a data-structure which represents functions from indices to terms, providing efficient versions of the following operations:

```ocaml
type subst

val apply : subst -> int -> term
val id : subst
val shift : int -> subst
val cons : term -> subst -> subst
val skip : int -> subst -> subst
val up : int -> subst -> subst
```

`subst` is the type of substitutions, i.e. functions from indices to terms. If `s` is a substitution we write `s i` for the application of `s` to an index `i : int`. The operations on substitutions behave as follows:
- `apply s i` applies the substitution `s` to the index `i`.
- `id` is the identity substitution which maps `i` to `Var i`.
- `shift k` adds `k` to every index: it maps `i` to `Var (i + k)`.
- `cons t s` is a substitution which maps `0` to `t` and `i + 1` to `s i`. It is typically used to implement beta reduction: `App (Lam body, arg)` beta-reduces to `substitute (cons arg id) body`.
- `skip k s` is the composition of `s` followed by `shift k`.
- `up k s` is a substitution which lifts [s] under [k] binders. It maps `i` to `Var i` if `i < k`, and otherwise to `weaken k (s (i - k))`. It is typically used when pushing a substitution under binders: `substitute s (Lam t) = Lam (substitute (up 1 s) t)`.

Note that the interface is not minimal: for instance `shift k` can always be implemented as `skip k id`. We allow some redundancy to allow as many operations as possible to have efficient implementations.

## Warmup: explicit substitutions using closures

As a warmup, let us revisit our first implementation of substitutions as OCaml closures `int -> term` by implementing the interface.
```ocaml
(** We assume a function [weaken : int -> term -> term] such that [weaken k t] adds [k >= 0] to every free index in [t].

A very useful optimization is to ensure that [weaken 0 t] returns [t] in constant time (without traversing it). *)

type subst = int -> term

let apply s i : term = s i
let id : subst = fun i -> Var i
let shift k : subst = fun i -> Var (i + k)
let cons t s : subst = fun i -> if i = 0 then t else s (i - 1)
let up k s : subst = fun i -> if i < k then Var i else weaken k (s (i - k))
let skip k s : subst = fun i -> weaken k (s i)
```
This implementation should be self explanatory: in fact it is so simple that it can be considered as a **reference** implementation: all other implementations of explicit substitutions should behave in the same way as this one.

## Why is this slow?

The operations which build substitutions (e.g. `id` or `cons`) are very efficient because all they do is build a closure, which takes constant time. However applying a substitution to an index is very expensive, due to two reasons.

First, `skip` and `up` aren't smart about applying weakening. For instance applying `skip k1 (skip k2 s)` to the index `0` will result in `weaken k1 (weaken k2 (s 0))` which will traverse `s 0` twice. More sophisticated implementations can avoid weakening several times the same term.

Second, building a closure using the operations provided by the interface (e.g. `cons` or `skip`) builds a linked list structure in memory, and applying the closure needs to walk the entire linked list in the worst case. This issue is quite subtle: the time needed to apply a substitution `s` depends on the number of operations `k` which were used to build the substitution.

In general `k` may be smaller or larger than the number `n` of variables in the substitution's domain, and can grow arbitrarily large even for a fixed `n`. Take for instance the substitution obtained by iterating `skip 1` `k` times starting with the identity: `skip 1 (skip 1 (skip 1 ...))`. Applying this substitution takes time O(k), whereas applying the equivalent substitution `shift k` takes time O(1).

## Explicit substitutions using lists

Our first efficient implementation will represent a substitution as a list of terms `t_0, t_1, t_2, ...` which maps `i` to `t_i`. Additionally, in order for `shift` to avoid weakening every term `t_i`, we store an integer offset at the start of the list, in between every term `t_i`, and at the end of the list. Formally, we can define list-based substitutions as:
```ocaml
type subst = Nil of int | Cons of int * term * subst
```

To apply a substitution to an index `i` we walk through the list, accumulating the offsets until we reach the term `t_i`, and return `weaken total_offset t_i`. Formally we can define `apply` as:
```ocaml
(** [acc] accumulates the total offset since the start of the list. *)
let rec apply_rec (acc : int) (s : subst) (i : int) : term =
  match s with
  | Nil k -> Var (i + k + acc)
  | Cons (k, t, s) -> if i = 0 then weaken (k + acc) t else apply_rec (k + acc) s (i - 1)

let apply s i : term = apply_rec 0 s i
```

Once you understand how `apply` works it is faily easy to implement the other operations. `id` and `shift k` build an empty list:
```ocaml
let id = Nil 0
let shift k = Nil k
```

`cons` adds a term at the beginning to the list:
```ocaml
let cons t s = Cons (0, t, s)
```

`skip` modifies the first offset in the list:
```ocaml
let skip k0 s =
  match s with
  | Nil k -> Nil (k0 + k)
  | Cons (k, t, s) -> Cons (k0 + k, t, s)
```

`up` is built on top of `cons` and `skip`:
```ocaml
(** [cons_vars n s] builds the substitution [Var 0 :: Var 1 :: ... :: Var (n - 1) :: s] where [::] is infix notation for [cons]. *)
let rec cons_vars n s =
  if n <= 0 then s
  else cons_vars (n - 1) (cons (Var (n - 1)) s)

let up k s = cons_vars k (skip k s)
```

## Is this efficient yet?

How efficient is the above list-based implementation? Similarly to the closure-based implementation, most operations take constant time: `id`, `shift`, `cons`, `skip` run in O(1), and `up k` runs in O(k).

The main difference concerns `apply`. First, `apply` only performs weakening once no matter the substitution. For instance applying `skip k1 (skip k2 s)` to index `0` results in `weaken (k1 + k2) (s 0)`. This can cause a huge speedup in some cases!
Second, if we don't account for the cost of weakening, `apply` runs in O(n) where n is the number of variables in the substitution's domain. The cost of applying a substitution no longer depends on the way this substitution was built. This means we can be very liberal in how we build substitutions: applying `skip 1 (skip 1 (skip 1 (... id)))` now has the same time complexity as applying the equivalent substitution `shift k`.

## A primer on skewed lists

Our second implementation will improve on the previous one by using a **skewed list** instead of a regular list. In this section we give a gentle introduction to this data-structure.

Skewed lists are a functional data-structure which provides many of the same basic operations as regular lists:
```ocaml
(** A skewed list containing element of type ['a]. *)
type 'a skewed_list

(** The empty skewed list. *)
val nil : 'a skewed_list

(** Add an element to the front of a skewed list. *)
val cons : 'a -> 'a skewed_list -> 'a skewed_list

(** Lookup the [i]-th element in a skewed list. *)
val nth : int -> 'a skewed_list -> 'a
```

Just like regular lists, `nil` and `cons` take constant time. However `nth` takes time O(log n) where n is the length of the list: this is much faster than regular lists for which `nth` takes time O(n).