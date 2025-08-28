
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

module Nat =
 struct
  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')
 end

(** val add1 : nat -> nat **)

let add1 n =
  S n

(** val sum : nat list -> nat **)

let rec sum = function
| Nil -> O
| Cons (x, xs') -> add x (sum xs')

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (x, xs') -> Cons ((f x), (map f xs'))

(** val inc_all : nat list -> nat list **)

let inc_all xs =
  map add1 xs

(** val evenb : nat -> bool **)

let rec evenb = function
| O -> True
| S n0 -> (match n0 with
           | O -> False
           | S k -> evenb k)

type person = { pid : nat; age : nat }

(** val can_vote : person -> bool **)

let can_vote p =
  Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))) p.age
