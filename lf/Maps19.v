(** ** Maps19: Inductively Defined Relations and Induction Principles *)

(** Adapted for SemProg@FAU 2013--2019 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import ssreflect ssrbool ssrfun.

(** This time, we import more than usual! *)

Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.

(** Aaand this. Do you still remember what it was? *)

Require Import Coq.Logic.FunctionalExtensionality.


(* ================================================================= *)
(** ** Maps: Total and Partial Maps *)

(** Maps (or dictionaries) are ubiquitous data structures, both in
    software construction generally and in the theory of programming
    languages in particular; we're going to need them in many places
    in the coming chapters.  They also make a nice case study using
    ideas we've seen in previous chapters, including building data
    structures out of higher-order functions (from [Basics] and
    [Poly]) and the use of reflection to streamline proofs (from
    [IndProp]).

    We'll define two flavors of maps: _total_ maps, which include a
    "default" element to be returned when a key being looked up
    doesn't exist, and _partial_ maps, which return an [option] to
    indicate success or failure.  The latter is defined in terms of
    the former, using [None] as the default element. *)


(* ================================================================= *)
(** ** Identifiers *)

(** First, we need a type for the keys that we use to index into our
    maps.  For this purpose, we will simply use plain [string]s.  Yes, Coq  has them!*)

(** To compare strings, we define the function [beq_string], which
    internally uses the function [string_dec] from Coq's string library.
    We then establish its fundamental properties. *)

Definition beq_string x y :=
  if string_dec x y then true else false.

(** 
 -  The function [string_dec] comes from Coq's string library.
 -  The result type of [string_dec] is neither [bool] nor [Prop], but rather a type that looks
    like [{x = y} + {x <> y}], called a [sumbool], which can be
    thought of as an "evidence-carrying boolean."  
 -  As you can imagine, it achieves something similar to reflect. 
 -  This type is not uncommon to see in Coq developments, so let us practice with it a little. *)

Check string_dec.

Lemma beq_stringP {x y}: reflect (x = y) (beq_string x y).
Proof.
  case E: (beq_string x y); constructor;
    case S: (string_dec x y) => [hP | hP] //;
        rewrite /beq_string S /is_left in E; discriminate.
Defined.

(** Do you understand what happened here? *)

(** Let us now put our reflection skills to good use... *)

Theorem beq_string_refl : forall s, true = beq_string s s.
Proof.
  (* WORKED IN CLASS *)
  move => s. case E: (beq_string s s ) => //.
  by move /beq_stringP in  E. 
Qed.

(** The following useful property of [beq_string] follows from an
    analogous lemma about strings: *)

Theorem beq_string_true_iff : forall x y : string,
  beq_string x y = true <-> x = y.
Proof.
  (* WORKED IN CLASS *)
  split.
  - by move /beq_stringP.
  - move => ->. by rewrite -beq_string_refl.
Qed.    

(** The next one could have been done similarly, but there's an even quicker way.*)

Theorem beq_string_false_iff : forall x y : string,
  beq_string x y = false
  <-> x <> y.
Proof.
  move => x y.
  by rewrite -beq_string_true_iff not_true_iff_false.
Qed.

(** This useful variant follows just by rewriting: *)

Theorem false_beq_string : forall x y : string,
   x <> y -> beq_string x y = false.
Proof.
  move => x y.
  by rewrite beq_string_false_iff.
Qed.



(* ================================================================= *)
(** ** Total Maps *)


(** Our main job in this chapter is to build a definition of
    partial maps using _functions_, rather
    than lists of key-value pairs, to build maps.
  - The advantage of
    this representation is that it offers an _extensional_ view of
    maps: two maps that respond to queries in the same way will
    be represented as literally the same thing (the same function),
    rather than just "equivalent" data structures.. *)

(**
    We build partial maps in two steps.  First, we define a type of
    _total maps_ that return a default value when we look up a key
    that is not present in the map. *)

Definition total_map (A:Type) := string -> A.

(** Intuitively, a total map over an element type [A] _is_ just a
    function that can be used to look up [id]s, yielding [A]s. *)

(**
    The function [t_empty] yields an empty total map, given a default
    element; this map always returns the default element when applied
    to any id. *)

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

(** More interesting is the [update] function, which (as before) takes
    a map [m], a key [x], and a value [v] and returns a new map that
    takes [x] to [v] and takes every other key to whatever [m] does. *)

Definition t_update {A:Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if beq_string x x' then v else m x'.

(** This definition is a nice example of higher-order programming.
    The [t_update] function takes a _function_ [m] and yields a new
    function [fun x' => ...] that behaves like the desired map. *)

(** For example, we can build a map taking [string]s to [bool]s, where
    ["foo"] and ["bar"] are mapped to [true] and every other key is
    mapped to [false], like this: *)

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

(** It's awkward to write such things, so we define new notations. *)

Notation "[< n >]" := (t_empty n) (at level 30).
Notation "st [< x ~~>> n >]" := (t_update st x n) (at level 21, left associativity).


Print examplemap.

(** Also, let us note that there is  notation for string equality. *)

Search "=?".

(** Moreover, the string library already provides reflection for equality ... *)

Check eqb_spec.



(** This completes the definition of total maps.  Note that we don't
    need to define a [find] operation because it is just function
    application! *)

Example update_example1 : examplemap "fau" = false.
Proof. by []. Qed.



Example update_example4 : examplemap "foo" = true.
Proof. by []. Qed.

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** To use maps in later chapters, we'll need several fundamental
    facts about how they behave. 
    Some of the proofs require the functional
    extensionality axiom discussed in the [Logic] chapter, which can be found
    in the standard library and it's imported here. *)

(** First, if we update a map [m] at a key [x] with a new value [v]
    and then look up [x] in the map resulting from the [update], we
    get back [v]: *)

Lemma t_update_eq : forall A (m: total_map A) x v,
   m [<x ~~>> v>] x = v.
Proof.
  (* WORKED IN CLASS *)
  move=> A m x v.
  by rewrite /t_update -beq_string_refl.
Qed.

(** On the other hand, if we update a map [m] at a key [x1] and then
    look up a _different_ key [x2] in the resulting map, we get the
    same result that [m] would have given. *)

(** Here's a little function that might prove useful: *)

Check negbTE.

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  m [<x1 ~~>> v>] x2 = m x2.
Proof.
  (* WORKED IN CLASS *)
  rewrite /t_update.
  by move => ? v x1 x2 m /beq_stringP/negbTE ->.
Qed.

(** If we update a map [m] at a key [x] with a value [v1] and then
    update again with the same key [x] and another value [v2], the
    resulting map behaves the same (gives the same result when applied
    to any key) as the simpler map obtained by performing just
    the second [update] on [m]: *)

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    m [<x ~~>> v1>] [<x ~~>> v2>]
  = m [<x ~~>> v2>].
Proof.
  (* WORKED IN CLASS *)
  move=> ? ? ? ? x1. apply: functional_extensionality => x2.
  by rewrite /t_update; case: beq_stringP.
Qed.

(** Could this one work w/o functional extensionality? *)

(** Using the example in chapter [IndProp] as a template, use
    [beq_stringP] to prove the following theorem, which states that if we
    update a map to assign key [x] the same value as it already has in
    [m], then the result is equal to [m]: *)

Theorem t_update_same : forall X x (m : total_map X),
  m [<x ~~>> m x>] = m.
Proof.
  (* WORKED IN CLASS *)
  move=> X x1 m. apply: functional_extensionality => x2.
  rewrite /t_update. case: beq_stringP => //.
  by move=> ->.
Qed.

(** Again, could this one work w/o functional extensionality? *)



(** Use [beq_stringP] to prove one final property of the [update]
    function: If we update a map [m] at two distinct keys, it doesn't
    matter in which order we do the updates. *)

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
    m [<x2 ~~>> v2>] [<x1 ~~>> v1>]
  =  m [<x1 ~~>> v1>] [<x2 ~~>> v2>].
Proof.
  (* WORKED IN CLASS *)
  move=> X v1 v2 x1 x2 m H.
  apply: functional_extensionality => x3.
  move: H.
  rewrite /t_update.
  move/beq_stringP/negbTE => H.
  case: beq_stringP => //.
  by move=> <-; rewrite H.
Qed.

(** Once again, could this one work w/o functional extensionality? *)

(* ################################################################# *)
(** * Partial maps *)

(** Finally, we define _partial maps_ on top of total maps.  A partial
    map with elements of type [A] is simply a total map with elements
    of type [option A] and default element [None]. *)

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Notation "**" := empty (at level 30).


Definition update {A:Type} (m : partial_map A)
                  (x : string) (v : A) :=
  t_update m x (Some v).

Notation "cxt ',,' x ':->' v " := (update cxt x v) (at level 21).

(** Notation is somewhat different; the reason is we want to use it also, e.g., when talking about contexts in of simply typed lambda calculus in future ... *)

(** We can now lift all of the basic lemmas about total maps to
    partial maps.  *)

Lemma update_eq : forall A (m: partial_map A) x v,
  (m,, x :-> v) x = Some v.
Proof.
  by move=> A m x v; rewrite /update t_update_eq.
Qed.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
  x2 <> x1 ->
  (m,, x2 :-> v) x1 = m x1.
Proof.
  by move=> X v x1 x2 m H; rewrite /update t_update_neq.
Qed.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
  m,, x :-> v1,, x :-> v2 = m,, x :-> v2.
Proof.
  by move=> A m v1 v2 x1; rewrite /update t_update_shadow.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  m,, x :-> v = m.
Proof.
  by move=> X v x m H; rewrite /update -H; apply: t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 <> x1 ->
    m,, x2 :-> v2,, x1 :-> v1
  = m,, x1 :-> v1,, x2 :-> v2.
Proof.
  by move=> X v1 v2 x1 x2 m; rewrite /update; apply: t_update_permute.
Qed.


(* Sun Jul 14 22:07:54 MSK 2019 *)
