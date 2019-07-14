(** ** IndRel19: Inductively Defined Relations and Induction Principles *)

(** Adapted from _Software Foundations_  for SemProg@FAU 2013--2019 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import ssreflect ssrbool ssrfun.

Require Import PeanoNat. (* for basic properties of [nat] functions! *)
Import Nat.

(* ================================================================= *)
(** ** Inductive Relations *)

(** A proposition parameterized by a number (such as [ev])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module LeModule.

(** One useful example is the "less than or equal to"
    relation on numbers. *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

(* Inductive le : nat -> nat -> Prop := *)
(*   | le_n : forall n, le n n *)
(*   | le_S : forall n m, (le n m) -> (le n (S m)). *)

Inductive le (n: nat) : nat -> Prop := 
   | le_n : le n n
   | le_S : forall m, (le n m) -> (le n (S m)). 

(* Locate "<=". *)
 Notation "m <= n" := (le m n).

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) -> 2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  do 3!(apply le_S). apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  case E : _ / => [| n H] //. 
  case F : _ / H; by rewrite F in E.
Qed.

(** Note it would be possible to define our relation in an almost identical way: *)

Inductive le' : nat -> nat -> Prop := 
   | le'_n : forall n, le' n n 
   | le'_S : forall n m, (le' n m) -> (le' n (S m)). 

(** But proving lemmas like the one one above using the [ssreflect] strategy would get somewhat more difficult. You can try it and see what would get problematic... *)

Theorem test_le'3 :
  (le' 2 1) -> 2 + 2 = 5.
Proof.

  case E : _ _ /  => [n | n m H] //.

  (** Here we can still handle the first case... *)

    by rewrite -E.

    (** But what now? The goal you are seeing now is simply nonsensical, even though there is nothing obviously inconsistent in the premises. If it is not obvious yet, try:*)

   rewrite !add_succ_l !add_succ_r.

   (** Not looking good, is it? *)

Abort.

(** We see here one of advantages of reasons why chosing one of arguments to be a parameter might be a good design choice. More will be seen when we discuss the shape of automatically generated induction principles later in this lecture. Let us also mention that similar problems may occur in the context of, e.g., formalizations of homotopy type theory in Coq. *)



(** The "strictly less than" relation [n < m] can be defined
    in terms of [le]. *)

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

End LeModule.

(** In fact, this relation is already defined: *)

Print le.
Print Peano.le.

(* => Inductive le (n : nat) : nat -> Prop :=
     le_n : n <= n | le_S : forall m : nat, n <= m -> n <= S m *)

(** Similarly,  [lt] is also already there:  *)

Print lt.
Print Peano.lt.

(* => lt = fun n : nat => [eta le  Peano.le (S n)]
     : nat -> nat -> Prop *)

(** Obviously, [le] has its own reflection view: *)


 
Check leb_spec0.

(* => leb_spec0
     : forall x y : nat, reflect (x <= y) (x <=? y) *)



(** Some other simple relations on numbers: *)

Inductive square_of  (n : nat) : nat -> Prop :=
  sq : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** Define an inductive binary relation [full_relation] that holds
    between every pair of natural numbers. *)

(** Define then the corresponding (trivial) fuction [full] on booleans and provide (trivial) reflection view [fullP]. *) 

(* FILL IN HERE *)

(** Now for a change define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

(** Define then the corresponding (trivial) fuction [empty] on booleans and provide (trivial) reflection view [emptyP]. *) 

(* FILL IN HERE *)



(** Recall what we said last time:  [Prop] and [bool] are complementary: [Prop] allows robust natural
    deduction, [bool] allows brute-force evaluation. *)

(** As you may guess, overusing inductively defined relations/propositions is not entirely in the spirit of [ssreflect]. Its design principle  is to reflect such relations and propositions as  recursive functions into booleans wherever possible. But it is not always possible, and one of the reasons has to do with differences between classical and constructive logic. Besides, while such functions are better suited for direct computations in Gallina, inductively defined propositions can often be better candidates for inductive proofs. *)

(** In fact, speaking of induction: with the Curry-Howard correspondence and its realization in Coq in
    mind, we can now take a deeper look at induction principles. *)

(* ################################################################# *)
(** * Induction Principles *)

(** 
  - Every time we declare a new [Inductive] datatype, Coq
    automatically generates an _induction principle_ for this type.
  - This induction principle is a theorem like any other: If [t] is
    defined inductively, the corresponding induction principle is
    called [t_ind].  
  - Here is the one for natural numbers: *)

Check nat_ind.
(*  ===> nat_ind :
           forall P : nat -> Prop,
              P 0  ->
              (forall n : nat, P n -> P (S n))  ->
              forall n : nat, P n  *)

(**
  - The [induction] tactic of  plain [Ltac] is a straightforward wrapper that, at its
    core, simply performs [apply t_ind]. [elim] does more, but it does use [t_ind].
  - To see this more clearly,
    let's experiment with directly using [apply nat_ind], instead of
    the [induction] tactic, to carry out some proofs.
  - Here, for
    example, is an alternate proof of a theorem that we saw earlier. *)

Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  by apply: nat_ind.
Qed.

(**
    These generated principles follow a similar pattern. If we define
    a type [t] with constructors [c1] ... [cn], Coq generates a
    theorem with this shape:

    t_ind : forall P : t -> Prop,
              ... case for c1 ... ->
              ... case for c2 ... -> ...
              ... case for cn ... ->
              forall n : t, P n
*)

(**
    The specific shape of each case depends on the arguments to the
    corresponding constructor.  Before trying to write down a general
    rule, let's look at some more examples. First, an example where
    the constructors take no arguments: *)

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.
(* ===> yesno_ind : forall P : yesno -> Prop,
                      P yes  ->
                      P no  ->
                      forall y : yesno, P y *)

(** **** Exercise: 1 star, standard, optional (rgb)  

    Write out the induction principle that Coq will generate for the
    following datatype.  Write down your answer on paper or type it
    into a comment, and then compare it with what Coq prints. *)

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.
Check rgb_ind.
(** [] *)

(** Here's another example, this time with one of the constructors
    taking some arguments. *)

Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.

Check natlist_ind.

    
(* ===> (Modulo a little variable renaming)
   natlist_ind :
      forall P : natlist -> Prop,
         P nnil  ->
         (forall (n : nat) (l : natlist),
            P l -> P (ncons n l)) ->
         forall n : natlist, P n *)

(** **** Exercise: 1 star, standard, optional (natlist1)  

    Suppose we had written the above definition a little
   differently: *)

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

(** Now what will the induction principle look like? 

    [] *)

(** From these examples, we can extract this general rule:

    - The type declaration gives several constructors; each
      corresponds to one clause of the induction principle.
    - Each constructor [c] takes argument types [a1] ... [an].
    - Each [ai] can be either [t] (the datatype we are defining) or
      some other type [s].
    - The corresponding case of the induction principle says:

        - "For all values [x1]...[xn] of types [a1]...[an], if [P]
          holds for each of the inductive arguments (each [xi] of type
          [t]), then [P] holds for [c x1 ... xn]".

*)

(** **** Exercise: 1 star, standard, optional (byntree_ind)  

    Write out the induction principle that Coq will generate for the
    following datatype.  (Again, write down your answer on paper or
    type it into a comment, and then compare it with what Coq
    prints.) *)

Inductive byntree : Type :=
 | bempty : byntree
 | bleaf  : yesno -> byntree
 | nbranch : yesno -> byntree -> byntree -> byntree.
(** [] *)

(** **** Exercise: 1 star, standard, optional (ex_set)  

    Here is an induction principle for an inductively defined
    set.

      ExSet_ind :
         forall P : ExSet -> Prop,
             (forall b : bool, P (con1 b)) ->
             (forall (n : nat) (e : ExSet), P e -> P (con2 n e)) ->
             forall e : ExSet, P e

    Give an [Inductive] definition of [ExSet]: *)

Inductive ExSet : Type :=
  (* FILL IN HERE *)
.
(** [] *)

(* ################################################################# *)
(** * Polymorphism *)

(** Next, what about polymorphic datatypes?

    The inductive definition of polymorphic lists

      Inductive list (X:Type) : Type :=
        | nil : list X
        | cons : X -> list X -> list X.

    is very similar to that of [natlist].  The main difference is
    that, here, the whole definition is _parameterized_ on a set [X]:
    that is, we are defining a _family_ of inductive types [list X],
    one for each [X].  (Note that, wherever [list] appears in the body
    of the declaration, it is always applied to the parameter [X].)
 *)

(**
    The induction principle is likewise parameterized on [X]:

     list_ind :
       forall (X : Type) (P : list X -> Prop),
          P [] ->
          (forall (x : X) (l : list X), P l -> P (x :: l)) ->
          forall l : list X, P l

    Note that the _whole_ induction principle is parameterized on
    [X].  That is, [list_ind] can be thought of as a polymorphic
    function that, when applied to a type [X], gives us back an
    induction principle specialized to the type [list X]. *)

(** **** Exercise: 1 star, standard, optional (tree)  

    Write out the induction principle that Coq will generate for
   the following datatype.  Compare your answer with what Coq
   prints. *)

Inductive tree (X:Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.
Check tree_ind.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Exercises *)
(** **** Exercise: 1 star, standard, optional (mytype)  

    Find an inductive definition that gives rise to the
    following induction principle:

      mytype_ind :
        forall (X : Type) (P : mytype X -> Prop),
            (forall x : X, P (constr1 X x)) ->
            (forall n : nat, P (constr2 X n)) ->
            (forall m : mytype X, P m ->
               forall n : nat, P (constr3 X m n)) ->
            forall m : mytype X, P m
*) 
(** [] *)

(** **** Exercise: 1 star, standard, optional (foo)  

    Find an inductive definition that gives rise to the
    following induction principle:

      foo_ind :
        forall (X Y : Type) (P : foo X Y -> Prop),
             (forall x : X, P (bar X Y x)) ->
             (forall y : Y, P (baz X Y y)) ->
             (forall f1 : nat -> foo X Y,
               (forall n : nat, P (f1 n)) -> P (quux X Y f1)) ->
             forall f2 : foo X Y, P f2
*) 
(** [] *)



(** **** Exercise: 1 star, standard, optional (foo')  

    Consider the following inductive definition: *)

Inductive foo' (X:Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.

(** What induction principle will Coq generate for [foo']?  Fill
   in the blanks, then check your answer with Coq.)

     foo'_ind :
        forall (X : Type) (P : foo' X -> Prop),
              (forall (l : list X) (f : foo' X),
                    _______________________ ->
                    _______________________   ) ->
             ___________________________________________ ->
             forall f : foo' X, ________________________
*)

(** [] *)


(** 
   - Interestingly, we can get induction to work with our self-written induction principles--provided we prove first these new induction principles do the job, of course! 
   - Some theorems can be proved slightly more conveniently this way... *)

(* ================================================================= *)
(** ** Explicit Proof Objects for Induction *)

    
(** Recall the induction principle on naturals that Coq generates for
    us automatically from the Inductive declation for [nat]. *)

Check nat_ind.
(* ===> 
   nat_ind : forall P : nat -> Prop,
      P 0 -> 
      (forall n : nat, P n -> P (S n)) -> 
      forall n : nat, P n  *)

(** There's nothing magic about this induction lemma: it's just
   another Coq lemma that requires a proof.  Coq generates the proof
   automatically too...  *)

Print nat_ind.
Print nat_rect.
(* ===> (after some manual inlining and tidying)
   nat_ind =
    fun (P : nat -> Prop) 
        (f : P 0) 
        (f0 : forall n : nat, P n -> P (S n)) =>
          fix F (n : nat) : P n :=
             match n with
            | 0 => f
            | S n0 => f0 n0 (F n0)
            end.
 *)

(** Note the use of inlined [fix] here. *)

(** We can read this as follows: 
     Suppose we have evidence [f] that [P] holds on 0,  and 
     evidence [f0] that [forall n:nat, P n -> P (S n)].  
     Then we can prove that [P] holds of an arbitrary nat [n] via 
     a recursive function [F].  [F] pattern matches on [n]: 
      - If it finds 0, [F] uses [f] to show that [P n] holds.
      - If it finds [S n0], [F] applies itself recursively on [n0] 
         to obtain evidence that [P n0] holds; then it applies [f0] 
         on that evidence to show that [P (S n)] holds. 
    [F] is just an ordinary recursive function that happens to 
    operate on evidence in [Prop] rather than on terms in [Set].
 
*)

(** We can adapt this approach to proving [nat_ind] to help prove
    _non-standard_ induction principles too. Recall our definition of [ev]: *)

 
Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).
 
 
(**    Recall also our desire to
    prove that

    [forall n : nat, even n -> ev n].
 
    Attempts to do this by standard induction on [n] fail, because the
    induction principle only lets us proceed when we can prove that
    [even n -> even (S n)] -- which is of course never provable.  We could prove it by induction on evidence, we could also do  a bit of a hack:
 
    [Theorem even__ev : forall n : nat,
     (even n -> ev n) /\ (even (S n) -> ev (S n))].
 *)

(**
 
   But we can make a much better proof by defining and proving a
    non-standard induction principle that goes "by twos":
 
 *)
 
 Definition nat_ind2 : 
    forall (P : nat -> Prop), 
    P 0 -> 
    P 1 -> 
    (forall n : nat, P n -> P (S(S n))) -> 
    forall n : nat , P n :=
       fun P => fun P0 => fun P1 => fun PSS => 
          fix f (n:nat) := match n with 
                             0 => P0 
                           | 1 => P1 
                           | S (S n') => PSS n' (f n') 
                           end.

 (** Again, note the use of inlined [fix] here. *)
 
 
 
Lemma even__ev' : forall n, even n -> ev n.
Proof.
 move => n.
 elim n using nat_ind2 => /= [Hev | |n' IHn' Hev].   (** <- da liegt der Hund begraben! *)
  -  apply ev_0.  
  -  by case H': _ /.  
  -  (* do you understand why [Hev] looks the way it does? *)
     by apply ev_SS, IHn'. 
Qed. 


(* ================================================================= *)
(** ** Setoid Rewriting *)

(** 
 -  Finally, something which is quite orthogonal to [ssreflect] way of doing things, and contents of today's lecture ...
 -  Some of Coq's tactics treat [iff] statements specially, avoiding
    the need for some low-level proof-state manipulation.  
 -  In particular, [rewrite] and some of its relatives can be used with [iff]
    statements, not just equalities.  To enable this behavior, we need
    to import a Coq library that supports it: *)

Require Import Coq.Setoids.Setoid.

(** Here is a simple example demonstrating how these tactics work with
    [iff].  First, let's use a couple of basic iff equivalences... *)

Check eq_mul_0.

(* => eq_mul_0
     : forall n m : nat, n * m = 0 <-> n = 0 \/ m = 0 *)

Check or_assoc.

(** We can now use these facts with [rewrite] and [reflexivity] to
    give smooth proofs of statements involving equivalences.  Here is
    a ternary version of the previous [mult_0] result: *)

Theorem mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof. 
  move => n m p.
  rewrite !eq_mul_0. (* see what happened? And we finish the same way: *)
  by rewrite or_assoc.
Qed.

(** 
   - "Setoid" is a set equipped with (well-behaved) equivalence relation. 
   - Uses of setoid rewriting go beyond equivalence in [Prop]. 
   - Esp. in  [ssreflect] style, you often want to transform  [Prop] equivalence to [bool] equivalence ... *)

(** To finish with setoid [iff], the [apply] tactic can also be used with [<->]. When given an
    equivalence as its argument, [apply] tries to guess which side of
    the equivalence to use. *)

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply eq_mul_0. apply H.
Qed.


(* Sun Jul 14 22:07:54 MSK 2019 *)
