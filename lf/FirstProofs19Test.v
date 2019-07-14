Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF19 Require Import FirstProofs19.

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

From LF19 Require Import FirstProofs19.
Import Check.

Goal True.

idtac "-------------------  mult_S_1  --------------------".
idtac " ".

idtac "#> mult_S_1".
idtac "Possible points: 2".
check_type @mult_S_1 ((forall n m : nat, m = S n -> m * (1 + n) = m * m)).
idtac "Assumptions:".
Abort.
Print Assumptions mult_S_1.
Goal True.
idtac " ".

idtac "-------------------  identity_fn_applied_twice  --------------------".
idtac " ".

idtac "#> identity_fn_applied_twice".
idtac "Possible points: 2".
check_type @identity_fn_applied_twice (
(forall f : bool -> bool,
 (forall x : bool, f x = x) -> forall b : bool, f (f b) = b)).
idtac "Assumptions:".
Abort.
Print Assumptions identity_fn_applied_twice.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 4".
idtac "Max points - advanced: 4".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- mult_S_1 ---------".
Print Assumptions mult_S_1.
idtac "---------- identity_fn_applied_twice ---------".
Print Assumptions identity_fn_applied_twice.
idtac "".
idtac "********** Advanced **********".
Abort.

(* Sun Jul 14 22:07:04 MSK 2019 *)

(* Sun Jul 14 22:07:54 MSK 2019 *)
