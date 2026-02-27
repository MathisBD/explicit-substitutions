# Three implementations of explicit substitutions

I recently stumbled upon the implementation of explicit substitutions used in the kernel of the Rocq theorem prover (file `kernel/esubst.ml`). The implementation -- due to Pierre-Marie Pédrot -- is fairly sophisticated and to the best of my knowledge hasn't been described anywhere. It is based on a fancy data-structure known as "skewed lists enriched over a monoid". But before we dive into the gory details of the implementation, let me set the scene.

## Lambda terms

In this blog post we will work with the standard (untyped) lambda calculus, which consists of variables, applications, and lambda abstractions:
```
t ::= x            (variable)
    | t u          (application)
    | fun x => t   (lambda abstraction)
```

To represent lambda terms in a programming language (OCaml will be our language of choice in this blog post), one has to choose a representation for variables. Using strings is not a good idea, for reasons we will not dive into here. A popular option is to use de Bruijn indices: a variable occurence is represented by an integer `i >= 0` which refers to the `i`-th binder counting upwards:
```ocaml
type term =
| Var of int
| App of term * term
| Lam of term
```
De Bruijn indices are notably found in the implementations of modern theorem provers (e.g. Rocq, Agda, Lean). Some example lambda terms are:
- The identity function `fun x => x` encoded as `Lam (Var 0)`.
- The first projection `fun x y => x` encoded as `Lam (Lam (Var 1))`.
- The second projection `fun x y => y` encoded as `Lam (Lam (Var 0))`.

## Parallel substitution

A pervasive operation on lambda terms is _parallel substitution_, which replaces all of the free variables in a term with new terms. Because of the many quirks of de Bruijn indices, this is actually quite tricky to implement efficiently. The remainder of this blog post gently builds up to an efficient implementation.

Let us first consider a simple but inefficient implementation of parallel substitution. Given a term `t : term` and a substitution `s : int -> term` which maps indices to terms, we can substitute with `s` in `t` as follows:
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

Unfortunately, as I will explain below this implementation of based on closure `int -> term` is very inefficient.

## An interface for explicit substitutions

Taking a step back, notice that although we think of substitutions as functions from `int` to `term`, we don't **need** to represent them using OCaml functions. All we need in order to implement the function `substitute` of the previous section is a type `subst` of substitutions, along with functions which allow us to build substitutions and to apply a substitution to an index:
```ocaml
type subst

val apply : subst -> int -> term
val id : subst
val shift : int -> subst
val cons : term -> subst -> subst
val skip : int -> subst -> subst
val up : int -> subst -> subst
```

`subst` is the type of substitutions, i.e. a particular encoding of functions from indices to terms. If `s` is a substitution we write `s i` for the application of `s` to an index `i >= 0`. The operations on substitutions behave as follows:
- `apply s i` applies the substitution `s` to the index `i`.
- `id` is the identity substitution which maps `i` to `Var i`.
- `shift k` adds `k` to every index: it maps `i` to `Var (i + k)`.
- `cons t s` is a substitution which maps `0` to `t` and `i + 1` to `s i`. It is typically used to implement beta reduction: `App (Lam body, arg)` beta-reduces to `substitute (cons arg id) body`.
- `skip k s` is the composition of `s` followed by `shift k`.
- `up k s` is a substitution which lifts `s` under `k` binders. It maps `i < k` to `Var i`, and `i >= k` to `weaken k (s (i - k))`. It is typically used when pushing a substitution under binders: `substitute s (Lam t) = Lam (substitute (up 1 s) t)`.

Note that this interface is not minimal: for instance `shift k` can always be implemented as `skip k id`. We allow some redundancy to allow as many operations as possible to have efficient implementations.

Another observation is that any substitution built using only the operations provided by the interface behaves as `fun i -> i + k` once the input `i` becomes sufficiently large. In fact, in a dependently typed language a standard trick is to index substitutions: `subst n m` is the type of functions which take as input an index `i < n` and produce a term with free indices `< m`. We will not do this here, but it is still useful to think of substitutions as functions with a finite domain: for instance if the domain of `s` is `[0..n-1]` then the domain of `up k s` is `[0..n+k-1]`.

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
It should be fairly clear that this indeed implements the interface given above. In fact this implementation is so simple that it can be considered as a **reference** implementation: all other implementations of explicit substitutions should behave in the same way as this one.

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

let apply s i = apply_rec 0 s i
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

Skewed lists are a functional data-structure which provides many of the operations of regular lists:
```ocaml
(** A skewed list containing elements of type ['a]. *)
type 'a skewed_list

(** The empty skewed list. *)
val nil : 'a skewed_list

(** Add an element to the front of a skewed list. *)
val cons : 'a -> 'a skewed_list -> 'a skewed_list

(** Lookup the [i]-th element in a skewed list. *)
val lookup : int -> 'a skewed_list -> 'a
```

The main advantage of skewed lists is that `lookup` runs on O(log n), while preserving the O(1) running time of `nil` and `cons`.

The basic idea of skewed lists is to represent a list not as a sequence of elements, but rather as a sequence of complete binary trees of elements:
```ocaml
type 'a tree = Leaf of 'a | Node of 'a * 'a tree * 'a tree
type 'a skewed_list = Nil | Cons of int * 'a tree * 'a skewed_list
```

`Nil` represents the empty list, and `Cons (n, t, l)` represents the list obtained by flattening the tree `t` of size `n` and concatenating it with the tail of the list `l`:
```ocaml
let rec flatten (t : 'a tree) : 'a list =
  match t with
  | Leaf x -> [ x ]
  | Node (x, t1, t2) -> x :: flatten t1 @ flatten t2
```

In a skewed list `Cons (n1, t1, Cons (n2, t2, Cons (n3, t3, ...)))` we maintain the invariant that
the trees `t1`, `t2`, `t3`, ... are complete binary trees of increasing sizes, and at most the first two trees can have the same size. Thanks to this invariant, in a skewed list with `n` elements the number of `Cons` cells is O(log n) and the depth of each tree is O(log n).

Implementing `nil`, `cons`, and `lookup` is a fun exercise (try it!): you need to take care of preserving the invariant when implementing `cons`, which requires possibly merging the trees in the first two `Cons` cells.

## Explicit substitutions using skewed lists

Recall our list-based implementation of substitutions: the only inefficient operation was `apply`. This is where skewed lists come in, allowing us to bring the running time of `apply` from O(n) down to O(log n).

Just as before we also store integer offsets between every element, so our tree type is slightly more involved compared to the previous section:
```ocaml
type tree =
| Leaf of { k : int; t : term }
| Node of { k : int; k_tot : int; t : term; left : tree; right : tree }
```

If we think in terms of substitutions,
- `Leaf { k; t }` represents the substitution `skip k (cons t id)`.
- `Node { k; k_tot; t; left; right }` represents the substitution `skip k (cons t (app left right))` where `app` is the n-ary version of `cons` (defined as you would expect).

The field `k_tot` is used to perform caching: `k_tot` is equal to the sum of offsets stored in the tree, which can be defined as:
```ocaml
total_offset (Leaf { k }) = k
total_offset (Node { k ; left ; right }) = k + total_offset left + total_offset right
```

A substitution is represented as a list of trees:
```ocaml
type subst = Nil of int | Cons of int * tree * subst
```
- `Nil k` represents the substitution `shift k`. In particular `Nil 0` is the identity.
- `Cons (n, t, s)` represents the substitution `cons t s`, where `t` is a complete binary tree of size `n`. Thus `n` is equal to `2^h - 1` where `h` is the height of `t`. Note that a `Cons` node doesn't need to contain an offset, because the tree `t` can itself contain offsets.

Just as with a regular skewed list, we maintain the invariant that in a substitution `Cons (_, t1, Cons (_, t2, Cons (_, t3, ...)))` the trees `t1`, `t2`, `t3`, ... have increasing sizes, and at most the first two trees can have the same size.

## Defining `apply`

As with our list-based implementation, the most difficult part is defining the function `apply`. We start with `apply_tree acc n t i` which applies the substitution defined by the tree `t` of size `n` to an index `i < n`. The argument `acc` accumulates offsets as we descend in the tree.
```ocaml
let rec apply_tree (acc : int) (n : int) (tr : tree) (i : int) : term =
  match tr with
  | Leaf { k; t } -> weaken (acc + k) t
  | Node { k; t; left; right } ->
      if i = 0 then
        weaken (acc + k) t
      else if i <= n / 2 then
        apply_tree (acc + k) (n / 2) left (i - 1)
      else
        apply_tree (acc + k + total_offset left) (n / 2) right (i - 1 - (n / 2))
```
In the `Node` case, we use the function `total_offset` to accumulate the total offset stores in the left subtree. The whole reason why we have a field `k_tot` is to implement `total_offset` in constant time:
```ocaml
let total_offset t =
  match t with Leaf { k } -> k | Node { k_tot } -> k_tot
```

Applying a substitution is then defined as:
```ocaml
(** [acc] accumulates the total offset since the start of the list. *)
let rec apply_rec (acc : int) (s : subst) (i : int) : term =
  match s with
  | Nil k -> Var (i + k + acc)
  | Cons (n, t, s) ->
      if i < n then apply_tree acc n t i
      else apply_rec (acc + total_offset t) s (i - n)

let apply s i = apply_rec 0 s i
```

## Other operations

The other operations are straightforward to implement. `id` and `skip` build an empty list:
```ocaml
let id = Nil 0
let shift k = Nil k
```

`cons` needs to check whether the first two trees have the same size, and if so merge them:
```ocaml
let cons t s =
  match s with
  | Cons (n1, left, Cons (n2, right, tail)) when n1 = n2 ->
      let k_tot = total_offset left + total_offset right in
      Cons (1 + n1 + n2, Node { k = 0; k_tot; t; left; right }, tail)
  | _ -> Cons (1, Leaf { k = 0; t }, s)
```

`skip` simply increments the offset of the first tree:
```ocaml
(** [skip_tree k t] adds [k] to the offset of the tree [t]. *)
let skip_tree k0 (tr : tree) : tree =
  match tr with
  | Leaf { k; t } -> Leaf { k = k + k0; t }
  | Node { k; k_tot; t; left; right } ->
      Node { k = k + k0; k_tot = k_tot + k0; t; left; right }

let skip k0 s =
  match s with
  | Nil k -> Nil (k0 + k)
  | Cons (n, t, s) -> Cons (n, skip_tree k0 t, s)
```

And finally `up` is defined using `skip` and `cons`, just as in the list-based implementation.

## Closing thoughts and other implementations of substitutions

Using a first-order (or _defunctionalized_) representation of substitutions has the benefit that one can apply simplifications when building substitutions, for instance `up k id = id` or `cons (Var k) (shift (1 + 1)) = shift k`. These simplifications can be used with any first-order representation of substitutions, including both list-based implementations described above. In particular these simplifications can be used to ensure that the identity substitution (and in general `shift k` for any `k`) has a unique representation, which allows one to quickly test whether a substitution behaves like the identity.

The skewed list implementation is very efficient: every operation takes constant time except for `apply` which takes O(log n). However there is another common operation on substitutions which can't be implemented efficiently using skewed lists, namely composition:
```ocaml
val compose : subst -> subst -> subst
```
Unfortunately composition of `s1` followed by `s2` requires applying `s2` to every term stored in `s1`, which is potentially very slow. For this reason skewed lists might not be the most efficient option depending on your specific use case.

If you need fast composition, a defunctionalized version of the closure-based implementation might be well suited:
```ocaml
type subst =
| Id
| Shift of int
| Cons of term * subst
| Skip of int * subst
| Up of int * subst
| Compose of subst * subst
```

On the other hand, if you don't need the `cons` operation you get thinnings, which represent strictly order-preserving maps `int -> int`. These can be implemented even more efficiently and with a much more compact representation using a bitset: I learned this trick in the paper "Builtin Types Viewed as Inductive Families" by Guillaume Allais.