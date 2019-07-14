Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF19 Require Import Basics19.

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

From LF19 Require Import Basics19.
Import Check.

Goal True.

idtac "-------------------  nandb  --------------------".
idtac " ".

idtac "#> BoolPlayground.test_nandb4".
idtac "Possible points: 1".
check_type @BoolPlayground.test_nandb4 (
(BoolPlayground.nandb BoolPlayground.true BoolPlayground.true =
 BoolPlayground.false)).
idtac "Assumptions:".
Abort.
Print Assumptions BoolPlayground.test_nandb4.
Goal True.
idtac " ".

idtac "-------------------  andb3  --------------------".
idtac " ".

idtac "#> BoolPlayground.test_andb34".
idtac "Possible points: 1".
check_type @BoolPlayground.test_andb34 (
(BoolPlayground.andb3 BoolPlayground.true BoolPlayground.true
   BoolPlayground.false = BoolPlayground.false)).
idtac "Assumptions:".
Abort.
Print Assumptions BoolPlayground.test_andb34.
Goal True.
idtac " ".

idtac "-------------------  leb'  --------------------".
idtac " ".

idtac "#> leb'".
idtac "Possible points: 1".
check_type @leb' ((nat -> nat -> bool)).
idtac "Assumptions:".
Abort.
Print Assumptions leb'.
Goal True.
idtac " ".

idtac "-------------------  ltb  --------------------".
idtac " ".

idtac "#> test_ltb3".
idtac "Possible points: 1".
check_type @test_ltb3 (((4 <? 2) = false)).
idtac "Assumptions:".
Abort.
Print Assumptions test_ltb3.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 4".
idtac "Max points - advanced: 4".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- BoolPlayground.test_nandb4 ---------".
Print Assumptions BoolPlayground.test_nandb4.
idtac "---------- BoolPlayground.test_andb34 ---------".
Print Assumptions BoolPlayground.test_andb34.
idtac "---------- leb' ---------".
Print Assumptions leb'.
idtac "---------- test_ltb3 ---------".
Print Assumptions test_ltb3.
idtac "".
idtac "********** Advanced **********".
Abort.

(* Sun Jul 14 22:07:04 MSK 2019 *)

(* Sun Jul 14 22:07:54 MSK 2019 *)
