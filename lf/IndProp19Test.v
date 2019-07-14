Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF19 Require Import IndProp19.

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

From LF19 Require Import IndProp19.
Import Check.

Goal True.

idtac "-------------------  ev_even_iff  --------------------".
idtac " ".

idtac "#> ev_even_iff".
idtac "Possible points: 2".
check_type @ev_even_iff (
(forall n : nat, ev n <-> (exists k : nat, n = PeanoNat.Nat.double k))).
idtac "Assumptions:".
Abort.
Print Assumptions ev_even_iff.
Goal True.
idtac " ".

idtac "-------------------  ev_sum  --------------------".
idtac " ".

idtac "#> ev_sum".
idtac "Possible points: 2".
check_type @ev_sum ((forall n m : nat, ev n -> ev m -> ev (n + m))).
idtac "Assumptions:".
Abort.
Print Assumptions ev_sum.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 4".
idtac "Max points - advanced: 4".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- ev_even_iff ---------".
Print Assumptions ev_even_iff.
idtac "---------- ev_sum ---------".
Print Assumptions ev_sum.
idtac "".
idtac "********** Advanced **********".
Abort.

(* Sun Jul 14 22:07:06 MSK 2019 *)

(* Sun Jul 14 22:07:54 MSK 2019 *)
