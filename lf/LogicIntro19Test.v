Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF19 Require Import LogicIntro19.

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

From LF19 Require Import LogicIntro19.
Import Check.

Goal True.

idtac "-------------------  and_exercise  --------------------".
idtac " ".

idtac "#> and_exercise".
idtac "Possible points: 2".
check_type @and_exercise ((forall n m : nat, n + m = 0 -> n = 0 /\ m = 0)).
idtac "Assumptions:".
Abort.
Print Assumptions and_exercise.
Goal True.
idtac " ".

idtac "-------------------  contrapositive  --------------------".
idtac " ".

idtac "#> contrapositive".
idtac "Possible points: 2".
check_type @contrapositive ((forall P Q : Prop, (P -> Q) -> ~ Q -> ~ P)).
idtac "Assumptions:".
Abort.
Print Assumptions contrapositive.
Goal True.
idtac " ".

idtac "-------------------  not_both_true_and_false  --------------------".
idtac " ".

idtac "#> not_both_true_and_false".
idtac "Possible points: 1".
check_type @not_both_true_and_false ((forall P : Prop, ~ (P /\ ~ P))).
idtac "Assumptions:".
Abort.
Print Assumptions not_both_true_and_false.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 5".
idtac "Max points - advanced: 5".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- and_exercise ---------".
Print Assumptions and_exercise.
idtac "---------- contrapositive ---------".
Print Assumptions contrapositive.
idtac "---------- not_both_true_and_false ---------".
Print Assumptions not_both_true_and_false.
idtac "".
idtac "********** Advanced **********".
Abort.

(* Sun Jul 14 22:07:06 MSK 2019 *)

(* Sun Jul 14 22:07:54 MSK 2019 *)
