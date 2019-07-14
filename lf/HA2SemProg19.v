(** ** HA2SemProg19: Properties and logic *)



(* ================================================================= *)
(** ** SemProg SoSe 2019, Set 2  *)

(** Submit your solutions  via StudOn until _Thu, June 13 @ 13:00_.  **)


(**
  - Please do not change the file name.
  - Do not post your solution in any publically available location.
  - Please submit on time, late solutions not accepted.
  - Before submission, please check from command line if your script compiles.
    In other words, do run [coqc] to make sure it accepts your file. If it doesn't, no points can be awarded.
  - Please submit _only_ the source file of the solution, i.e., [*.v]! Compiled output [*.vo] is useless for submission and will not get you any points. Compile the file for testing, not in order to submit compilation output to me.
  - Also, remember it will be run on a different machine which does not have the
    same folder structure as yours... Please bear this in mind and be careful
    with using load paths (absolute or relative) in your scripts.
  - If you resubmit a solution on StudOn (which is always possible before the
    deadline), please make sure to delete the old
    ones! And make sure that the final submission has the right name. Remember
    all submissions will be downloaded together as a bunch and fed through a
    script. Having more than one solution from a given person messes up
    automation.
*)
  

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import ssreflect ssrbool ssrfun.

(** Using [ssreflect] is not obligatory.  *)

From Coq Require Import List.
Import List.ListNotations.

(** ... and also, for [beq_nat], instead of loading it from [Basics19.v] ... *)
Import Nat.
From Coq Require Import Arith.
Notation "x =? y" := (beq_nat x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope. (* [leb] comes from [Nat] *)


(* ================================================================= *)
(** ** Exercise 1: constructive quantification *)

(** **** Exercise: 3 stars, standard (quantifiers)  *)

(** Many of familiar laws for quantifiers still hold for constructive logic. Here and everywhere below you can actually provide a normal tactic proof if writing down proof term provides too difficult.  *)

Definition notexists_forallnot : forall (X:Type) (P : X -> Prop),
  ~ (exists x : X, P x) -> (forall x : X, ~ P x) 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition forallnot_notexists : forall (X:Type) (P : X -> Prop),
  (forall x, ~ P x) ->  ~ (exists x, P x) 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition forallnot_equiv_notexists : forall (X:Type) (P : X -> Prop),
  (forall x, ~ P x) <->  ~ (exists x, P x) 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition forallnotnot_equiv_notexistsnot : forall (X:Type) (P : X -> Prop),
  (forall x, ~ ~ P x) <->  ~ (exists x, ~ P x) 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Lemma  CEpqENpNq : forall P Q, (P <-> Q) -> (~P <-> ~Q).
Proof.
  (* FILL IN HERE *) Admitted.

Definition notforallnot_equiv_notnotexists : forall (X:Type) (P : X -> Prop),
    ~(forall x, ~ P x) <->  ~ ~ (exists x, P x) 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition existsnot_notforall : forall (X:Type) (P : X -> Prop),
    (exists x, ~ P x) -> ~ (forall x,  P x) 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition forall_notexistsnot : forall (X:Type) (P : X -> Prop),
    (forall x, P x) -> ~ (exists x, ~ P x) 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** How about the converse of the last one? As it turns out, it requires
    classical logic, see below ... *)

(** [] *)

(* ================================================================= *)
(** ** Exercise 2: classical axioms *)

(** **** Exercise: 4 stars, standard (classical_axioms)  *)

(** Let us have a closer look on the behaviour of classical propositions in Coq. *)

(** Here are several "classical" properties and axioms. When universally
    quantified over all propositions, all of them imply each other. Sometimes,
    it makes sense to state them for individual propositions too, especially in
    the context of reflection with boolean functions we are going to discuss later. *)

(** Recall again: here and everywhere below you can actually provide a normal tactic proof if writing down proof term provides too difficult.  *)

Definition em_for_P (P : Prop) := P \/ ~P.
(** The above is sometimes called _decidability_ for [P], but in Coq one should
    be slightly careful about this name. *)
Definition peirce_for_P (P:Prop) := forall Q: Prop,
  ((P->Q)->P)->P.
Definition dn_elimination_for_P (P : Prop) := 
  ~ ~P -> P.
Definition de_morgan_not_and_not_forPQ  (P Q:Prop) :=
  ~(~P /\ ~Q) -> P\/Q.
Definition implies_to_or_forPQ (P Q:Prop) :=
  (P->Q) -> (~P\/Q).

Definition excluded_middle := forall P, em_for_P P.
Definition peirce := forall P, peirce_for_P P.
Definition double_negation_elimination := forall P:Prop, dn_elimination_for_P P.
Definition de_morgan_not_and_not := forall P Q:Prop, de_morgan_not_and_not_forPQ P Q.
Definition implies_to_or := forall P Q:Prop, implies_to_or_forPQ P Q.

(** Fill in the definitions: *)

Definition ito__em :
  implies_to_or -> excluded_middle   
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition em__itoP : forall P,
    em_for_P P -> forall Q, implies_to_or_forPQ P Q   
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.


Definition em__ito :
  excluded_middle -> implies_to_or 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition em__demorgan :
  excluded_middle -> de_morgan_not_and_not 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.


Definition em__dneP : forall P, 
    em_for_P P -> dn_elimination_for_P P 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
           
Definition em__dne : 
  excluded_middle -> double_negation_elimination 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.


Definition dne__demorganPQ : forall P Q,
    (dn_elimination_for_P (P \/ Q)) -> (de_morgan_not_and_not_forPQ P Q) 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
  
Definition dne__demorgan :
  double_negation_elimination -> de_morgan_not_and_not 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition demorgan__em : de_morgan_not_and_not -> excluded_middle 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.


Definition  em__peirceP : forall P,
    (em_for_P P) -> peirce_for_P P 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition em__peirce :
  excluded_middle -> peirce 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
               
Lemma peirce__em :
  peirce -> excluded_middle.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Exercise 3: reflection yields classical properties *)

(** **** Exercise: 2 stars, standard (reflect_classical)  *)

(** This exercise requires a notion introduced in the lecture on May 24. Being reflected ensures validity of classical laws: *)

Theorem reflect_classical : forall P b, reflect P b ->
                                 (forall Q, implies_to_or_forPQ P Q) /\
                                      peirce_for_P P /\
                                      dn_elimination_for_P P.
Proof.
  (* FILL IN HERE *) Admitted.

Corollary reflect_disj : forall P Q b, reflect (P \/ Q) b -> de_morgan_not_and_not_forPQ P Q.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)



(* ================================================================= *)
(** ** Exercise 4: Reflection for predicates on lists *)

(** **** Exercise: 3 stars, standard (forall2P)  *)

(** The standard library offers an inductive predicate for comparing lists wrt to a given binary relation *)

Print Forall2.

(* ==>
[
Inductive Forall2 (A B : Type) (R : A -> B -> Prop) : list A -> list B -> Prop :=
    Forall2_nil : Forall2 R [] []
  | Forall2_cons : forall (x : A) (y : B) (l : list A) (l' : list B),
                   R x y -> Forall2 R l l' -> Forall2 R (x :: l) (y :: l')
]
 *)

(** First, let us recall what it means for a relation to be reflected by a binary function. *)

Definition Rreflected {A B : Type} (R : A -> B -> Prop) (f: A -> B -> bool) :=
  forall a b, reflect (R a b) (f a b).

(** Define its boolean counterpart. It might be a good idea to do pattern matching on two arguments at the same time. *)

Fixpoint  forall2 {A B : Type} (R : A -> B -> Prop)  (f: A -> B -> bool) (P: Rreflected R f) (la: list A) (lb : list B) : bool (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** In the following proof, you might: 
  - want to think whether you do induction first, or rather apply some trivial reflection view first to split the goal
  - recall you can handle boolean conjunctions with [move => /andP ...]
  - realize that (instantiated) premises can be also used as reflection views. 
*)

Theorem forall2P {A B : Type} (R : A -> B -> Prop) (f: A -> B -> bool) : forall (P: Rreflected R f), Rreflected (Forall2 R) (forall2 R f P).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Exercise 5: Kuroda and some classical aspects of negation *)

(** **** Exercise: 3 stars, standard  (notexistsnot_forall)  *)

(** Just like in the propositional case, there are many propositions which
    cannot be proved in the intuitionistic logic, but are not as strong as
    classical axioms either. Here is a famous example: *)

Definition kuroda (X:Type) (P : X -> Prop) := (forall x, ~ ~ P x) -> ~ ~(forall x, P x).

(** This law of course trivially follows from classical logic. *)

(** Here and everywhere below you can actually provide a normal tactic proof if writing down proof term provides too difficult.  *)

Definition classic_kuroda : forall X P, (forall (x : X), em_for_P (P x)) -> kuroda X P 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
    
(** Do you think you can prove any of the classical axioms from [kuroda]? *)

(** Here is an example of a law governing the interaction of negation and
    quantification, which only requires the Kuroda axiom: *)

Definition notforall_notnotexistsnot :
  forall (X:Type) (P : X -> Prop), kuroda X P ->
                             ~ (forall x,  P x) -> ~ ~ (exists x, ~ P x) 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** However, there are laws which require more of classical logic. Some not all
    that much: *)

Theorem notexistsnot_forall :
  forall (X:Type) (P : X -> Prop),
  (forall x, em_for_P (P x)) ->
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ================================================================= *)
(** ** Optional exercises *)

(* ================================================================= *)
(** ** Exercise 6, optional: the drinker paradox *)

(** **** Exercise: 4 stars, standard, optional (the_drinker_paradox)  *)

(** But some theorems require more or less the full strength of classical
    logic... although as we will see in one of following exercises, even with
    these beasts it is still possible to be a bit more refined when approaching
    them from a constructive point of view. *)

Theorem notforallnot_exists : excluded_middle ->
  forall (X:Type) (P : X -> Prop),
   ~ (forall x, ~ P x) -> (exists x, P x) .
Proof.
  (* FILL IN HERE *) Admitted.

Theorem notforall_existsnot : excluded_middle ->
  forall (X:Type) (P : X -> Prop),
     ~ (forall x, P x) -> (exists x, ~ P x) .
Proof.
  (* FILL IN HERE *) Admitted.

(** And finally the difficult direction of the infamous _drinker paradox_ . Note
    that we need also to assume non-emptiness (inhabitation) of X for this one:
    we don't have it for free! *)

Definition inhabited (X : Type) := exists (x: X), x = x.

Theorem the_heart_of_the_drinker_paradox :  excluded_middle ->
  forall (R : Prop) (X: Type) (P : X -> Prop), inhabited X ->
    ((forall x : X, P x) -> R) -> (exists x, P x  -> R).
Proof.
  (* FILL IN HERE *) Admitted.

Corollary the_drinker_paradox : excluded_middle -> forall (R : Prop) (X: Type) (P : X -> Prop),  inhabited X -> (exists x, P x  <-> (forall x : X, P x)).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)


(* ================================================================= *)
(** ** Exercise 7, optional: constant domain *)

(** **** Exercise: 4 stars, standard, optional (notforall_existsnot_CD)  *)

(** Incidentally, some of laws above can be derived from axioms which do not
    rely on classical logic. *)

Definition constant_domain (X : Type) :=
  forall (P : X -> Prop) (Q: Prop), (forall  x, (P x \/ Q)) -> ((forall x, P x) \/ Q).

(** Here and everywhere below you can actually provide a normal tactic proof if writing down proof term provides too difficult.  *)


Theorem empty_domain_constant : forall X, ~(inhabited X) -> constant_domain X.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem bool_constant : constant_domain bool.
  (* FILL IN HERE *) Admitted.

Theorem em_constant : excluded_middle -> forall X, constant_domain X.
Proof.
  (* FILL IN HERE *) Admitted.

(** The constant domain axiom/property allows to get some existential
    quantification out of negated universal one... which, in general, is not a
    constructive thing: negating an universal sentence does not produce any
    witness! *)
 
Theorem CD_often_nonempty :
  forall (X: Type) (P : X -> Prop), constant_domain X ->  ~ (forall x, P x) -> inhabited X.
Proof.
  (* FILL IN HERE *) Admitted.    

(** And the connection between quantifiers becomes even better if the property
    in question behaves decently. *)

Definition wem_prop (X : Type) (P : X -> Prop) := forall (x : X), ~ (P x) \/ ~ ~ (P x).

(** [wem] here stands for _weak excluded middle_. Here is our final result about
    constant domains, which formalizes what I mean by an _even better
    connection_ between quantifiers. It may seem a non-exciting statement, but
    you need to be reasonably smart when looking for the right instance of the
    constant domain axiom. *)

Theorem notforall_existsnot_CD : forall (X:Type), constant_domain X ->                                             
  forall  (P : X -> Prop), wem_prop X P ->
     ~ (forall x,  ~ P x) -> (exists x, ~ ~ P x) .
Proof.
  (* FILL IN HERE *) Admitted.

(** Note that in light of [em_constant] earlier in this exercise, this would
    allow an alternative approach to proving [notforallnot_exists] and
    [notforall_existsnot] in the preceding exercise. *)

(** [] *)


(* ================================================================= *)
(** ** Exercise 8, optional: impredicative connectives *)

(** **** Exercise: 4 stars, standard, optional (impredicative)   *)

(** In constructive logic, it is known there is a way of defining all the
    logical connectives once we have universal quantification over propositions.
    Here is how it goes: please fill in all the missing proofs. **)

(** Note btw that these impredicative connectives are defined on [Prop] only.
    Hence, we are not going to run into problems that plagued us with
    impredicative quantification over [Types] when we discussed the issue during
    the lecture. *)

(** Here again you can actually provide a normal tactic proof if writing down proof term provides too difficult.  *)

Definition soFalse : Prop := forall B : Prop, B.

Definition so_False : soFalse <-> False 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition soneg (P: Prop) : Prop := forall B : Prop, P -> B.

Definition so_neg : forall (P : Prop), soneg P <-> (P -> soFalse) 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition soor (A B: Prop) : Prop := forall (Q: Prop), (A -> Q) -> (B -> Q) -> Q.



Definition so_or : forall (A B : Prop), (A \/ B) <-> (soor A B) 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition soand (A B: Prop) : Prop := forall (Q: Prop), (A -> B -> Q) ->Q.

Definition so_and : forall A B, (A /\ B) <-> (soand A B) 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Definition soexist (X : Type) (A : X -> Prop) : Prop := forall (P : Prop), (forall (x : X), (A x -> P)) -> P.



Definition so_exist : forall (X : Type) (A : X -> Prop), ((ex A) <-> (soexist X A)) 
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.



(** [] *)







(* Sun Jul 14 22:07:54 MSK 2019 *)
