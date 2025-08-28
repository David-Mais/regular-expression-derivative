
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

val add : nat -> nat -> nat

module Nat :
 sig
  val leb : nat -> nat -> bool
 end

val add1 : nat -> nat

val sum : nat list -> nat

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val inc_all : nat list -> nat list

val evenb : nat -> bool

type person = { pid : nat; age : nat }

val can_vote : person -> bool
