(** * Preamble: importing SSReflect / Mathcomp *)
Set Warnings "-notation-overridden".
From mathcomp Require Import
   ssreflect ssrfun ssrbool ssrnat eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*** Simple types *)

(** * Empty type *)
Inductive empty : Type :=
  .

(** * Unit type *)

Inductive unit : Type :=
  tt : unit.


(** * Boolean type *)

(*** Parametric types *)

(** * Product type *)

  (* Inductive prod (A B : Type) : Type := *)
  (*   | pair : A -> B -> prod A B. *)

  Locate "->".

(** * Sum type *)


  (* Inductive sum (A B : Type) : Type := *)
  (*   left : A -> sum A B *)
  (* | right : B -> sum A B. *)

(** * Example: building swap function *)

Definition swap (A B : Type) (p : A * B) : (B * A) :=
  let '(a, b) := p in
  (b, a).

Print prod.
Locate "/\".
Print and.
Definition swap' (A B : Type) : A * B -> B * A.
  case.
  move=> a b.
  split.
  exact: b.
  exact: a.
Defined.
Print swap'.

Lemma andC (A B : Prop) : A /\ B -> B /\ A.
Proof.
  case.
  move=> pa pb.
  split.
  exact: pb.
  exact: pa.
Qed.

(*** Recursive types *)

(** * Natural numbers *)

Print nat.

(*** Parametric recursive types *)

(** * Lists *)

Print seq.

(** * Binary Trees *)




(*** Dependent types *)


(** * Dependent function type *)

Locate "->".

(** * A rather silly example *)

Definition Foo (b : bool) : Type :=
  if b then nat else bool.

Fail Definition bar (b : bool) : Foo b :=
  if b return _ then 0 else false.

Definition bar (b : bool) : Foo b :=
  if b as b' return (Foo b') then 42 else false.



(** * Existential type *)

(* Inductive ex (A : Type) (P : A -> Prop) : Prop  := *)
(*    ex_intro : forall (x : A), P x      -> ex P. *)
(* pair     :   (a : A)  (b : B)  -> prod A B *)


(** * Equality type *)

(* Inductive eq (A : Type) (x : A) : A -> Prop := *)
(*   erefl : eq x x. *)

Print eq.
Locate "=".

Check erefl : (1 + 1) = 2 :> nat.


(** * Even numbers *)
Inductive ev : nat -> Prop :=
| ev0 : ev 0
| ev_step : forall n, ev n -> ev (S (S n)).


(*** Proofs *)

(* obligatory proof of associativity of some concrete monoid's operation :) *)

Lemma catA : forall (T : Type) (xs ys zs : seq T),
    xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof.
move=> T xs ys zs.
by elim: xs => // x xs' /= ->.
Qed.












(*** Totality *)

(* https://github.com/SimonBoulier/TypingFlags *)
From TypingFlags Require Import Loader.

(* Disable the positivity checking of inductive types and
   the termination checking of fixpoints *)
Unset Guard Checking.

(** * Elegant, but non-structural recursive [interleave] function *)

(* Fixpoint interleave_ns {T} (xs ys : seq T) {struct xs} : seq T :=  *)
(*   if xs is (x :: xs') then x :: interleave_ns ys xs' *)
(*   else ys. *)

(* Compute interleave_ns [:: 1; 3] [:: 2; 4]. *)

(* (* simple unit tests *) *)
(* Check erefl : interleave_ns [::] [::] = [::]. *)
(* Check erefl : interleave_ns [::] [:: 1] = [:: 1]. *)
(* Check erefl : interleave_ns [:: 1] [::] = [:: 1]. *)
(* Check erefl : interleave_ns [:: 1; 3] [:: 2; 4] = [:: 1; 2; 3; 4]. *)
(* Check erefl : interleave_ns [:: 1] [:: 2; 3] = [:: 1; 2; 3]. *)

(* Print Assumptions interleave_ns. *)



(* Fixpoint interleave {T} (xs ys : seq T) : seq T := *)
(*   match xs, ys with *)
(*   | (x :: xs'), (y :: ys') => x :: y :: interleave xs' ys' *)
(*   | [::], _ => ys *)
(*   | _, [::] => xs *)
(*   end. *)

(* Check erefl : interleave [::] [::] = [::]. *)
(* Check erefl : interleave [::] [:: 1] = [:: 1]. *)
(* Check erefl : interleave [:: 1] [::] = [:: 1]. *)
(* Check erefl : interleave [:: 1; 3] [:: 2; 4] = [:: 1; 2; 3; 4]. *)
(* Check erefl : interleave [:: 1] [:: 2; 3] = [:: 1; 2; 3]. *)

(* Lemma interleave_ns_eq_interleave {T} (xs ys : seq T) : *)
(*   interleave_ns xs ys = interleave xs ys. *)
(* Proof. *)
(* by elim: xs ys => //= x xs' IHxs' [|y ys'] //=; rewrite IHxs'. *)
(* Qed. *)

(* (** More ways of implementing [interleave] can be found here: *)
(* https://stackoverflow.com/a/48178543/2747511 *) *)




(* (** * Why do we require termination? *) *)

(* (** Let's prove False! *) *)
Fixpoint proof_of_False (n : nat) : False := proof_of_False n.

Print Assumptions proof_of_False.




(** * Strict positivity rule *)

Inductive prop :=
  RemoveNegation of (prop -> False).

Definition not_prop (p : prop) : False :=
  let '(RemoveNegation not_p) := p in not_p p.
Check not_prop : prop -> False.

Definition yet_another_proof_of_False : False :=
  not_prop (RemoveNegation not_prop).

Print Assumptions yet_another_proof_of_False.





(** * Type : Type *)

Check Type : Type.

Set Printing Universes.

Universe i j.

Fail Check Type@{i} : (Type@{i}).

Check Type@{i} : (Type@{j}).

Check nat.
Check Set.

Unset Printing Universes.

(* If you want more:
"One Monad To Prove Them All" by J. Christiansen, S. Dylus, F. Teegen(2018)
https://arxiv.org/abs/1805.08059
 *)
