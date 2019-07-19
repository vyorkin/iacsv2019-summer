(** * Blatt 1 --- Polymorphism and Tactics *)



(* ================================================================= *)
(** ** SemProg SoSe 2019, Set 1  *)

(** Submit your solutions  via StudOn until _Mon, May 20 @ 13:00_.  **)


(** - Please do not change the file name.

  - Do not post your solution in any publically available
    location.

  - Please submit on time, late solutions not accepted.

  - Before submission, please check from command line if your
    script compiles. In other words, do run [coqc] to make sure
    it accepts your file. If it doesn't, no points can be
    awarded.

  - Please submit _only_ the source file of the solution, i.e.,
    [*.v]! Compiled output [*.vo] is useless for submission and
    will not get you any points. Compile the file for testing,
    not in order to submit compilation output to me.

  - Also, remember it will be run on a different machine which
    does not have the same folder structure as yours... Please
    bear this in mind and be careful with using load paths
    (absolute or relative) in your scripts.

  - If you resubmit a solution on StudOn (which is always
    possible before the deadline), please make sure to delete
    the old ones! And make sure that the final submission has
    the right name. Remember all submissions will be downloaded
    together as a bunch and fed through a script. Having more
    than one solution from a given person messes up automation.
    *)


Set Warnings "-notation-overridden,-parsing".
From Coq Require Import ssreflect ssrbool ssrfun.

(** Using [ssreflect] is not obligatory.  *)

(** And instead of our list development in the [Poly19] chapter, let's go for the standard library ... *)

From Coq Require Import List.
Import List.ListNotations.

(** ... and also, for [beq_nat], instead of loading it from [Basics19.v] ... *)
Import Nat.
From Coq Require Import Arith.
Notation "x =? y" := (beq_nat x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope. (* [leb] comes from [Nat] *)

(* ================================================================= *)
(** ** Exercise 1 *)
(** **** Exercise: 3 stars, standard (fold)  *)

(** Recall the [fold] function. As it turns out, Coq's standard
library has two versions thereof: [fold_left] and [fold_right].
This is (almost) the one we've been working with. *)

Print fold_right.

(** Careful, in the lecture the order of type arguments was
opposite to those in the standard library. For consistency, we
flip them here, so it follows the lecture ordering. On the other
hand, we do not make type arguments of [fold] implict: even in
the lecture, it has caused us some problems, and in the case of
HA below thinking what the type argument should be is often the
first step to solve them. *)

Definition fold (A B: Type) f l b:= @fold_right B A f b l.

(** We did length in terms of [fold]. We can also define [map]
    in terms of [fold]. Finish [fold_map] below. *)

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold _ _ (fun x xs => f x :: xs) l nil.

(** Prove that fold_map is correct. *)

Theorem fold_map_correct : forall X Y (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  move => ? ? ? ?.
Qed.

(** Similarly ... *)

Definition fold_flat_map {X Y: Type} (f: X -> list Y) (l: list X) : list Y
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem fold_flat_map_correct : forall X Y (f : X -> list Y) (l : list X),
  fold_flat_map f l = flat_map f l.
Proof.
(* FILL IN HERE *) Admitted.

(** And finally, append itself can be defined in terms of fold *)

Definition fold_append {X : Type} (l l': list X) : list X
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem fold_append_correct : forall X (l l' : list X),
  fold_append l l' = app l l'.
Proof.
(* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Exercise 2 *)

(** **** Exercise: 3 stars, standard (partition)

    Use [filter] to write a Coq function [partition]:

  partition : forall X : Type,
              (X -> bool) -> list X -> list X * list X

   Given a set [X], a test function of type [X -> bool] and a [list
   X], [partition] should return a pair of lists.  The first member of
   the pair is the sublist of the original list containing the
   elements that satisfy the test, and the second is the sublist
   containing those that fail the test.  The order of elements in the
   two sublists should be the same as their order in the original
   list.
 *)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
(* FILL IN HERE *) Admitted.

Example test_partition2: partition (fun x => false) [5;9;0] = (nil, [5;9;0]).
(* FILL IN HERE *) Admitted.

Print fst.

(** Now prove the following characterization theorems for [partition]. Warning: you might need some material that is covered at the end of Tactics19. *)

Theorem partition_fst: forall (X : Type)  (test : X -> bool) (l : list X),
                         fold _ _ andb (map test (fst (partition test l))) true = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem partition_snd: forall (X : Type)  (test : X -> bool) (l : list X),
                         fold _ _ orb (map test (snd (partition test l))) false = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Exercise 3 *)
(** **** Exercise: 3 stars, standard (combine_after_split)  *)

(** We can prove that [split] and [combine] are inverses in one sense.
    Proof can be made very short, but requires some care and information from final parts of [Tactics19].
    In particular, you might need to:
    - make your induction hypothesis general enough
    - destruct compound expressions and not lose the information obtained
    - remember that not only lists, but also products are inductive datatypes  *)



Theorem combine_after_split : forall X Y (l : list (X * Y)),
  combine (fst (split l)) (snd (split l)) = l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Exercise 4 *)
(** **** Exercise: 3 stars, standard (combine_after_split)  *)

(** Now prove a partial converse to the above theorem. *)

Theorem split_after_combine :   forall (X Y:Type) (l1 : list X) (l2 : list Y),
    length l1 = length l2 -> split (combine l1 l2) = (l1, l2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Exercise 5: Church addition and multiplication *)

(** **** Exercise: 3 stars, standard (church_numerals)

    This exercise explores an alternative way of defining natural
    numbers, using the so-called _Church numerals_, named after
    mathematician Alonzo Church.  We can represent a natural number
    [n] as a function that takes a function [f] as a parameter and
    returns [f] iterated [n] times. *)

Definition nat := forall X : Type, (X -> X) -> X -> X.

(** Let's see how to write some numbers with this notation. Iterating
    a function once should be the same as just applying it. Thus, *)

Definition one : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** Similarly, [two] should apply [f] twice to its argument, etc: *)

Definition two : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition three : nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f (f x)).

(** Defining [zero] is somewhat trickier: how can we "apply a function
    zero times"? The answer is actually simple: just return the
    argument untouched. *)

Definition zero : nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(** More generally, a number [n] can be written as [fun X f x => f (f
    ... (f x) ...)], with [n] occurrences of [f].  *)

(** Complete the definitions of the following functions. Make sure
    that the corresponding unit tests pass by proving them with
    [reflexivity]. *)

(** Successor of a natural number: *)

Definition succ (n : nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example succ_1 : succ zero = one.
Proof. (* FILL IN HERE *) Admitted.

Example succ_2 : succ one = two.
Proof. (* FILL IN HERE *) Admitted.

Example succ_3 : succ two = three.
Proof. (* FILL IN HERE *) Admitted.

(** Addition of two natural numbers: *)

Definition plus (n m : nat) : nat  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example plus_1 : plus zero one = one.
Proof. (* FILL IN HERE *) Admitted.

Example plus_2 : plus two three = plus three two.
Proof. (* FILL IN HERE *) Admitted.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. (* FILL IN HERE *) Admitted.

(** Multiplication: *)

Definition mult (n m : nat) : nat  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example mult_1 : mult one one = one.
Proof. (* FILL IN HERE *) Admitted.

Example mult_2 : mult zero (plus three three) = zero.
Proof. (* FILL IN HERE *) Admitted.

Example mult_3 : mult two three = plus three three.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Bonus Exercise 6: Church exponentiation *)

(** **** Exercise: 3 stars, advanced (church_exponentiation)

    Exponentiation is somewhat more difficult. _Hint_: Polymorphism plays a
    crucial role here. However, choosing the right type to iterate over can be
    tricky. If you hit a "Universe inconsistency" error, try iterating over a
    different type: [nat] itself is usually problematic. *)

Definition exp (n m : nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example exp_1 : exp two two = plus two two.
Proof. (* FILL IN HERE *) Admitted.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. (* FILL IN HERE *) Admitted.

Example exp_3 : exp three zero = one.
Proof. (* FILL IN HERE *) Admitted.

(** [] *)

(* Sun Jul 14 22:07:53 MSK 2019 *)
