Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF19 Require Import HA2SemProg19.

Parameter MISSING: Type.

Module Check.

Ltac check_type A B :=
    match type of A with
    | context[MISSING] => idtac "Missing:" A
    | ?T => first [unify T B; idtac "Type: ok" | idtac "Type: wrong - should be (" B ")"]
    end.

Ltac print_manual_grade A :=
    match eval compute in A with
    | Some (_ ?S ?C) =>
        idtac "Score:"  S;
        match eval compute in C with
          | ""%string => idtac "Comment: None"
          | _ => idtac "Comment:" C
        end
    | None =>
        idtac "Score: Ungraded";
        idtac "Comment: None"
    end.

End Check.

From LF19 Require Import HA2SemProg19.
Import Check.

Goal True.

idtac "-------------------  quantifiers  --------------------".
idtac " ".

idtac "#> notexists_forallnot".
idtac "Possible points: 1".
check_type @notexists_forallnot (
(forall (X : Type) (P : X -> Prop),
 ~ (exists x : X, P x) -> forall x : X, ~ P x)).
idtac "Assumptions:".
Abort.
Print Assumptions notexists_forallnot.
Goal True.
idtac " ".

idtac "#> notforallnot_equiv_notnotexists".
idtac "Possible points: 1".
check_type @notforallnot_equiv_notnotexists (
(forall (X : Type) (P : X -> Prop),
 ~ (forall x : X, ~ P x) <-> ~ ~ (exists x : X, P x))).
idtac "Assumptions:".
Abort.
Print Assumptions notforallnot_equiv_notnotexists.
Goal True.
idtac " ".

idtac "#> forall_notexistsnot".
idtac "Possible points: 1".
check_type @forall_notexistsnot (
(forall (X : Type) (P : X -> Prop),
 (forall x : X, P x) -> ~ (exists x : X, ~ P x))).
idtac "Assumptions:".
Abort.
Print Assumptions forall_notexistsnot.
Goal True.
idtac " ".

idtac "-------------------  classical_axioms  --------------------".
idtac " ".

idtac "#> em__ito".
idtac "Possible points: 1".
check_type @em__ito ((excluded_middle -> implies_to_or)).
idtac "Assumptions:".
Abort.
Print Assumptions em__ito.
Goal True.
idtac " ".

idtac "#> em__dne".
idtac "Possible points: 1".
check_type @em__dne ((excluded_middle -> double_negation_elimination)).
idtac "Assumptions:".
Abort.
Print Assumptions em__dne.
Goal True.
idtac " ".

idtac "#> demorgan__em".
idtac "Possible points: 1".
check_type @demorgan__em ((de_morgan_not_and_not -> excluded_middle)).
idtac "Assumptions:".
Abort.
Print Assumptions demorgan__em.
Goal True.
idtac " ".

idtac "#> peirce__em".
idtac "Possible points: 1".
check_type @peirce__em ((peirce -> excluded_middle)).
idtac "Assumptions:".
Abort.
Print Assumptions peirce__em.
Goal True.
idtac " ".

idtac "-------------------  reflect_classical  --------------------".
idtac " ".

idtac "#> reflect_classical".
idtac "Possible points: 1".
check_type @reflect_classical (
(forall (P : Prop) (b : bool),
 Bool.reflect P b ->
 (forall Q : Prop, implies_to_or_forPQ P Q) /\
 peirce_for_P P /\ dn_elimination_for_P P)).
idtac "Assumptions:".
Abort.
Print Assumptions reflect_classical.
Goal True.
idtac " ".

idtac "#> reflect_disj".
idtac "Possible points: 1".
check_type @reflect_disj (
(forall (P Q : Prop) (b : bool),
 Bool.reflect (P \/ Q) b -> de_morgan_not_and_not_forPQ P Q)).
idtac "Assumptions:".
Abort.
Print Assumptions reflect_disj.
Goal True.
idtac " ".

idtac "-------------------  forall2P  --------------------".
idtac " ".

idtac "#> forall2P".
idtac "Possible points: 3".
check_type @forall2P (
(forall (A B : Type) (R : A -> B -> Prop) (f : A -> B -> bool)
   (P : @Rreflected A B R f),
 @Rreflected (list A) (list B) (@List.Forall2 A B R) (@forall2 A B R f P))).
idtac "Assumptions:".
Abort.
Print Assumptions forall2P.
Goal True.
idtac " ".

idtac "-------------------  notexistsnot_forall  --------------------".
idtac " ".

idtac "#> notforall_notnotexistsnot".
idtac "Possible points: 1".
check_type @notforall_notnotexistsnot (
(forall (X : Type) (P : X -> Prop),
 kuroda X P -> ~ (forall x : X, P x) -> ~ ~ (exists x : X, ~ P x))).
idtac "Assumptions:".
Abort.
Print Assumptions notforall_notnotexistsnot.
Goal True.
idtac " ".

idtac "#> notexistsnot_forall".
idtac "Possible points: 2".
check_type @notexistsnot_forall (
(forall (X : Type) (P : X -> Prop),
 (forall x : X, em_for_P (P x)) ->
 ~ (exists x : X, ~ P x) -> forall x : X, P x)).
idtac "Assumptions:".
Abort.
Print Assumptions notexistsnot_forall.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 15".
idtac "Max points - advanced: 15".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- notexists_forallnot ---------".
Print Assumptions notexists_forallnot.
idtac "---------- notforallnot_equiv_notnotexists ---------".
Print Assumptions notforallnot_equiv_notnotexists.
idtac "---------- forall_notexistsnot ---------".
Print Assumptions forall_notexistsnot.
idtac "---------- em__ito ---------".
Print Assumptions em__ito.
idtac "---------- em__dne ---------".
Print Assumptions em__dne.
idtac "---------- demorgan__em ---------".
Print Assumptions demorgan__em.
idtac "---------- peirce__em ---------".
Print Assumptions peirce__em.
idtac "---------- reflect_classical ---------".
Print Assumptions reflect_classical.
idtac "---------- reflect_disj ---------".
Print Assumptions reflect_disj.
idtac "---------- forall2P ---------".
Print Assumptions forall2P.
idtac "---------- notforall_notnotexistsnot ---------".
Print Assumptions notforall_notnotexistsnot.
idtac "---------- notexistsnot_forall ---------".
Print Assumptions notexistsnot_forall.
idtac "".
idtac "********** Advanced **********".
Abort.

(* Sun Jul 14 22:07:07 MSK 2019 *)

(* Sun Jul 14 22:07:55 MSK 2019 *)
