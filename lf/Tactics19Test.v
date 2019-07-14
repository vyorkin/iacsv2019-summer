Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF19 Require Import Tactics19.

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

From LF19 Require Import Tactics19.
Import Check.

Goal True.

idtac "-------------------  rev_exercise1  --------------------".
idtac " ".

idtac "#> rev_exercise1".
idtac "Possible points: 3".
check_type @rev_exercise1 (
(forall l l' : list nat, l = @List.rev nat l' -> l' = @List.rev nat l)).
idtac "Assumptions:".
Abort.
Print Assumptions rev_exercise1.
Goal True.
idtac " ".

idtac "-------------------  beq_nat_true  --------------------".
idtac " ".

idtac "#> beq_nat_true".
idtac "Possible points: 2".
check_type @beq_nat_true ((forall n m : nat, (n =? m) = true -> n = m)).
idtac "Assumptions:".
Abort.
Print Assumptions beq_nat_true.
Goal True.
idtac " ".

idtac "-------------------  destruct_eqn_practice  --------------------".
idtac " ".

idtac "#> bool_fn_applied_thrice".
idtac "Possible points: 2".
check_type @bool_fn_applied_thrice (
(forall (f : bool -> bool) (b : bool), f (f (f b)) = f b)).
idtac "Assumptions:".
Abort.
Print Assumptions bool_fn_applied_thrice.
Goal True.
idtac " ".

idtac "-------------------  beq_nat_sym  --------------------".
idtac " ".

idtac "#> beq_nat_sym".
idtac "Possible points: 3".
check_type @beq_nat_sym ((forall n m : nat, (n =? m) = (m =? n))).
idtac "Assumptions:".
Abort.
Print Assumptions beq_nat_sym.
Goal True.
idtac " ".

idtac "-------------------  filter_exercise  --------------------".
idtac " ".

idtac "#> filter_exercise".
idtac "Advanced".
idtac "Possible points: 3".
check_type @filter_exercise (
(forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
 @List.filter X test l = (x :: lf)%list -> test x = true)).
idtac "Assumptions:".
Abort.
Print Assumptions filter_exercise.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 10".
idtac "Max points - advanced: 13".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- rev_exercise1 ---------".
Print Assumptions rev_exercise1.
idtac "---------- beq_nat_true ---------".
Print Assumptions beq_nat_true.
idtac "---------- bool_fn_applied_thrice ---------".
Print Assumptions bool_fn_applied_thrice.
idtac "---------- beq_nat_sym ---------".
Print Assumptions beq_nat_sym.
idtac "".
idtac "********** Advanced **********".
idtac "---------- filter_exercise ---------".
Print Assumptions filter_exercise.
Abort.

(* Sun Jul 14 22:07:05 MSK 2019 *)

(* Sun Jul 14 22:07:54 MSK 2019 *)
