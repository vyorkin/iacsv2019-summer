Set Warnings "-notation-overridden,-parsing".
From Coq Require Export String.
From LF19 Require Import HA1SemProg19.

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

From LF19 Require Import HA1SemProg19.
Import Check.

Goal True.

idtac "-------------------  fold  --------------------".
idtac " ".

idtac "#> fold_map_correct".
idtac "Possible points: 1".
check_type @fold_map_correct (
(forall (X Y : Type) (f : X -> Y) (l : list X),
 @fold_map X Y f l = @List.map X Y f l)).
idtac "Assumptions:".
Abort.
Print Assumptions fold_map_correct.
Goal True.
idtac " ".

idtac "#> fold_flat_map_correct".
idtac "Possible points: 1".
check_type @fold_flat_map_correct (
(forall (X Y : Type) (f : X -> list Y) (l : list X),
 @fold_flat_map X Y f l = @List.flat_map X Y f l)).
idtac "Assumptions:".
Abort.
Print Assumptions fold_flat_map_correct.
Goal True.
idtac " ".

idtac "#> fold_append_correct".
idtac "Possible points: 1".
check_type @fold_append_correct (
(forall (X : Type) (l l' : list X), @fold_append X l l' = (l ++ l')%list)).
idtac "Assumptions:".
Abort.
Print Assumptions fold_append_correct.
Goal True.
idtac " ".

idtac "-------------------  partition  --------------------".
idtac " ".

idtac "#> test_partition1".
idtac "Possible points: 1".
check_type @test_partition1 (
(@partition Datatypes.nat Nat.odd
   (1 :: (2 :: 3 :: 4 :: 5 :: @nil Datatypes.nat)%list) =
 ((1 :: 3 :: 5 :: @nil Datatypes.nat)%list,
 (2 :: 4 :: @nil Datatypes.nat)%list))).
idtac "Assumptions:".
Abort.
Print Assumptions test_partition1.
Goal True.
idtac " ".

idtac "#> partition_fst".
idtac "Possible points: 1".
check_type @partition_fst (
(forall (X : Type) (test : X -> bool) (l : list X),
 fold bool bool andb
   (@List.map X bool test (@fst (list X) (list X) (@partition X test l)))
   true = true)).
idtac "Assumptions:".
Abort.
Print Assumptions partition_fst.
Goal True.
idtac " ".

idtac "#> partition_snd".
idtac "Possible points: 1".
check_type @partition_snd (
(forall (X : Type) (test : X -> bool) (l : list X),
 fold bool bool orb
   (@List.map X bool test (@snd (list X) (list X) (@partition X test l)))
   false = false)).
idtac "Assumptions:".
Abort.
Print Assumptions partition_snd.
Goal True.
idtac " ".

idtac "-------------------  combine_after_split  --------------------".
idtac " ".

idtac "#> combine_after_split".
idtac "Possible points: 3".
check_type @combine_after_split (
(forall (X Y : Type) (l : list (X * Y)),
 @List.combine X Y (@fst (list X) (list Y) (@List.split X Y l))
   (@snd (list X) (list Y) (@List.split X Y l)) = l)).
idtac "Assumptions:".
Abort.
Print Assumptions combine_after_split.
Goal True.
idtac " ".

idtac "-------------------  combine_after_split  --------------------".
idtac " ".

idtac "#> combine_after_split".
idtac "Possible points: 3".
check_type @combine_after_split (
(forall (X Y : Type) (l : list (X * Y)),
 @List.combine X Y (@fst (list X) (list Y) (@List.split X Y l))
   (@snd (list X) (list Y) (@List.split X Y l)) = l)).
idtac "Assumptions:".
Abort.
Print Assumptions combine_after_split.
Goal True.
idtac " ".

idtac "-------------------  church_numerals  --------------------".
idtac " ".

idtac "#> succ_3".
idtac "Possible points: 1".
check_type @succ_3 ((succ two = three)).
idtac "Assumptions:".
Abort.
Print Assumptions succ_3.
Goal True.
idtac " ".

idtac "#> plus_3".
idtac "Possible points: 1".
check_type @plus_3 ((plus (plus two two) three = plus one (plus three three))).
idtac "Assumptions:".
Abort.
Print Assumptions plus_3.
Goal True.
idtac " ".

idtac "#> mult_3".
idtac "Possible points: 1".
check_type @mult_3 ((mult two three = plus three three)).
idtac "Assumptions:".
Abort.
Print Assumptions mult_3.
Goal True.
idtac " ".

idtac "-------------------  church_exponentiation  --------------------".
idtac " ".

idtac "#> exp_3".
idtac "Advanced".
idtac "Possible points: 3".
check_type @exp_3 ((exp three zero = one)).
idtac "Assumptions:".
Abort.
Print Assumptions exp_3.
Goal True.
idtac " ".

idtac " ".

idtac "Max points - standard: 15".
idtac "Max points - advanced: 18".
idtac "".
idtac "********** Summary **********".
idtac "".
idtac "********** Standard **********".
idtac "---------- fold_map_correct ---------".
Print Assumptions fold_map_correct.
idtac "---------- fold_flat_map_correct ---------".
Print Assumptions fold_flat_map_correct.
idtac "---------- fold_append_correct ---------".
Print Assumptions fold_append_correct.
idtac "---------- test_partition1 ---------".
Print Assumptions test_partition1.
idtac "---------- partition_fst ---------".
Print Assumptions partition_fst.
idtac "---------- partition_snd ---------".
Print Assumptions partition_snd.
idtac "---------- combine_after_split ---------".
Print Assumptions combine_after_split.
idtac "---------- combine_after_split ---------".
Print Assumptions combine_after_split.
idtac "---------- succ_3 ---------".
Print Assumptions succ_3.
idtac "---------- plus_3 ---------".
Print Assumptions plus_3.
idtac "---------- mult_3 ---------".
Print Assumptions mult_3.
idtac "".
idtac "********** Advanced **********".
idtac "---------- exp_3 ---------".
Print Assumptions exp_3.
Abort.

(* Sun Jul 14 22:07:05 MSK 2019 *)

(* Sun Jul 14 22:07:54 MSK 2019 *)
