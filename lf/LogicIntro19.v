(** ** LogicIntro: Introduction to logic, propositions and proofs  *)

(** Adapted from _Software Foundations_  for SemProg@FAU 2013--2019 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import ssreflect ssrbool ssrfun.

(** In previous chapters, we have seen many examples of factual
    claims (_propositions_) and ways of presenting evidence of their
    truth (_proofs_).  In particular, we have worked extensively with
    _equality propositions_ of the form [e1 = e2], with
    implications ([P -> Q]), and with quantified propositions ([forall
    x, P]).  In this chapter, we will see how Coq can be used to carry
    out other familiar forms of logical reasoning.

    Before diving into details, let's talk a bit about the status of
    mathematical statements in Coq.  Recall that Coq is a _typed_
    language, which means that every sensible expression in its world
    has an associated type.  Logical claims are no exception: any
    statement we might try to prove in Coq has a type, namely [Prop],
    the type of _propositions_.  We can see this with the [Check]
    command: *)

Check 3 = 3.
(* ===> Prop *)

Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

(** Note that _all_ syntactically well-formed propositions have type
    [Prop] in Coq, regardless of whether they are true or not.

    Simply _being_ a proposition is one thing; being _provable_ is
    something else! *)

Check forall n : nat, n = 2.
(* ===> Prop *)

Check 3 = 4.
(* ===> Prop *)

(** Indeed, propositions don't just have types: they are _first-class
    objects_ that can be manipulated in the same ways as the other
    entities in Coq's world.  So far, we've seen one primary place
    that propositions can appear: in [Theorem] (and [Lemma] and
    [Example]) declarations. *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But propositions can be used in many other ways.  For example, we
    can give a name to a proposition using a [Definition], just as we
    have given names to expressions of other sorts. *)

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity.  Qed.

(** We can also write _parameterized_ propositions -- that is,
    functions that take arguments of some type and return a
    proposition. *)

(** For instance, the following function takes a number
    and returns a proposition asserting that this number is equal to
    three: *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)

(** In Coq, functions that return propositions are said to define
    _properties_ of their arguments.

    For instance, here's a (polymorphic) property defining the
    familiar notion of an _injective function_. *)

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  move=> n m. by case.
Qed.

(** The equality operator [=] is also a function that returns a
    [Prop].

    The expression [n = m] is syntactic sugar for [eq n m], defined
    using Coq's [Notation] mechanism. Because [eq] can be used with
    elements of any type, it is also polymorphic: *)

Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)

(** (Notice that we wrote [@eq] instead of [eq]: The type
    argument [A] to [eq] is declared as implicit, so we need to turn
    off implicit arguments to see the full type of [eq].) *)


(** This is a good opportunity to return to our slogan from the poster, recall ... *)

(** ... _proofs are programs and programs are proofs_! *)

(** Programming and proving in Coq are two sides of the same coin.
    Proving manipulates evidence, much as programs manipulate data. *)

(** "_Algorithms are the computational  content of proofs_."  --Robert Harper *)

(** Question: If evidence is data, what are propositions themselves?

    Answer: They are types! *)

(** Suppose we introduce an alternative pronunciation of "[:]". (In statements of theorems, not as a [ssreflect] tactical of course). 
    Instead of "has type," we can say "is a proof of" ... *) 

(** This pun between types and propositions -- between [:] as "has type"
    and [:] as "is a proof of" or "is evidence for" -- is called the
    _Curry-Howard correspondence_.  It proposes a deep connection
    between the world of logic and the world of computation:

                 propositions  ~  types
                 proofs        ~  data values

    Many useful insights follow from this connection. *)

(* ================================================================= *)
(** ** Understanding Prop and logic in Coq *)

(** 
  

    Question: _How do you define the meaning of a proposition_?  
    - begins with  the _Brouwer-Heyting-Kolmogorov interpretation_ of _intuitionistic_ logic proposed in the late 1920's and early 1930's
    - more recently, continues with Martin-L#&ouml;#f ...
*)

(** The meaning of a proposition is given by _rules_ and _definitions_
    that say how to construct _evidence_ for the truth of the
    proposition from other evidence.

    - Typically, rules are defined _inductively_, just like any other
      datatype.

    - Sometimes a proposition is declared to be true without
      substantiating evidence.  Such propositions are called _axioms_.

    In this, and subsequent chapters, we'll see more about how these
    proof terms work in more detail.

 *)

(* ================================================================= *)
(** ** Natural deduction *)

(** 
   - A formal calculus which makes this process of constructing evidence explicit is called _natural deduction_.
   - It was first proposed by Gerhard Gentzen in the 1930's. 
   -  It gives the meaning of each connective by its _introduction_ and destruction (_elimination_) rules. 
   - Those of you who have done a recent version of GLoIn, have seen a Fitch-style variant of ND. *)


(** 
  - From Coq's point of view, introduction rules say how to _prove_ a proposition involving a given connective. 
  - Elimination rules say how to _use_ or _apply_ hypotheses (or earlier lemmas) using this connective in new proofs.
  - What we are doing with Coq is assisted proof search. 
  - We start with the ultimate result we want to obtain, the sentence we want to hold true.
  - That is, we begin at the bottom of proof tree to be built and try find a way bottom-up to its branches: premises living in the context we have. *)



(* ================================================================= *)
(** ** Logical Connectives *)

(* ================================================================= *)
(** ** Conjunction *)

(** The _conjunction_ (or _logical and_) of propositions [A] and [B]
    is written [A /\ B], representing the claim that both [A] and [B]
    are true.

    The Brouwer-Heyting-Kolmogorov interpretation: a proof of [P /\ Q] is a pair [<a, b>] where [a] is a proof of [P] and [b] is a proof of [Q]. *)

(** Thus, its type is: *)

Check and.

(*  ===> 
    and: Prop -> Prop -> Prop *)

Print and.

(*  ===> 
   Inductive and (A B : Prop) : Prop :=  conj : A -> B -> A /\ B *)

(** Notice the similarity with the definition of the [prod] type,
    given in chapter [Poly]; the only difference is that [prod] takes
    [Type] arguments, whereas [and] takes [Prop] arguments. *)

Print prod.
(* ===>
   Inductive prod (A B : Type) : Type :=
   | pair : A -> B -> A * B. *)

(* ----------------------------------------------------------------- *)
(** *** Conjunction: proving it *)

(**

                         Gamma |- A    Gamma |- B
                         --------------------------                      (/\ I)
                             Gamma |- A /\ B

*)


(** To prove a conjunction in standard Ltac, one can use the [split] tactic.  It will generate
    two subgoals, one for each part of the statement: *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** In fact, for a type with a single constructor taking two arguments, [split] is just a wrapper for applying this constructor; in this case, [apply conj]. *)

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.

Proof.
  apply conj.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** In [ssreflect], our good old friend [by []] is more than enough. *)

Example and_example'' : 3 + 4 = 7 /\ 2 * 2 = 4.

Proof.
  by [].
Qed.

(** For any propositions [A] and [B], if we assume that [A] is true
    and we assume that [B] is true, we can conclude that [A /\ B] is
    also true. *)

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
    by [].
    (*
  intros A B HA HB. split.
  - apply HA.
  - apply HB.*)
Qed.

(** Since applying a theorem with hypotheses to some goal has the
    effect of generating as many subgoals as there are hypotheses for
    that theorem, we can apply [and_intro] to achieve the same effect
    as [split]. *)

Example and_example''' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (and_exercise)  *)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Conjunction: using it *)

(** So much for proving conjunctive statements.  To go in the other
    direction -- i.e., to _use_ a conjunctive hypothesis to prove
    something else -- we can destruct this inductive type, thus getting a proposition wrapped in its constructors. *)

(** In a natural deduction system, we _use_ conjunction via _elimination rules_: *)

(**

                               Gamma |- A /\ B
                             ---------------------                     (/\ E_l)
                                  Gamma |- A

                               Gamma |- A /\ B
                             ---------------------                     (/\ E_r)
                                  Gamma |- B

*)

(** For instance: *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  move => ? ?.
  case => [Hn Hm].
  rewrite Hn Hm.
  by [].
Qed.

(** As usual, we can also destruct [H] right when we introduce it,
    instead of introducing and then destructing it: *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  move => ? ? [Hn Hm].
  rewrite Hn Hm.
  by [].
  (* OR: intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.*)
Qed.


(** You may wonder why we bothered packing the two hypotheses [n = 0]
    and [m = 0] into a single conjunction, since we could have also
    stated the theorem with two separate premises: *)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** For this theorem, both formulations are fine.  But it's important
    to understand how to work with conjunctive hypotheses because
    conjunctions often arise from intermediate steps in proofs,
    especially in bigger developments.  Here's a simple example: *)

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

(** Another common situation with conjunctions is that we know
    [A /\ B] but in some context we need just [A] (or just [B])...
    *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
   (* WORKED IN CLASS *)
  move => ? ? [? ?]. by [].
  (*intros P Q [HP HQ].
  apply HQ.*)  Qed.
  

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  (* WORKED IN CLASS *)
  by move => ? ? [? ?]. 
  (*intros P Q [HP HQ].
  apply HQ.*)  Qed.
  

(** Finally, we sometimes need to rearrange the order of conjunctions
    and/or the grouping of multi-way conjunctions.  
    Commutativity and associativity theorems are handy... *)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
    by move => ? ? [? ?].
  (*intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.*)  Qed.
  
(** In the following proof of associativity, try to use the _nested_
    intro pattern to break the hypothesis...  *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  (* WORKED IN CLASS *)
  move => ? ? ? [? [? ?]]. by [].
  (*
  intros P Q R [HP [HQ HR]].  
  split.
  - (* left *) split.
    + (* left *) apply HP.
    + (* right *) apply HQ.
  - (* right *) apply HR.*)  Qed.

(* ----------------------------------------------------------------- *)
(** *** Who needs tactics when we have Gallina? *)

(** Tactic proofs (ordinary [Ltac] or [ssreflect]) are useful and convenient, but they are not
    essential: in principle, we can always construct the required
    evidence directly, using pattern-matching. Then we can use [Definition]
    (rather than [Theorem]) to give a global name directly to a
    piece of evidence. *)

Definition and_comm'_aux P Q (H : P /\ Q) :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

(** We have two parametric propositions here. But we could replace them with universally quantified ones. *)

(* ================================================================= *)
(** ** Universal quantifiers, implications and functions *)

(** In Coq's _computational_ universe (where data structures and
    programs live), there are two sorts of values with arrows in their
    types: _constructors_ introduced by [Inductive]-ly defined data
    types, and _functions_.

    Similarly, in Coq's _logical_ universe (where we carry out proofs),
    there are two ways of giving evidence for an implication:
    constructors introduced by [Inductive]-ly defined propositions,
    and... functions!

   Notice that both implication ([->]) and quantification ([forall])
    correspond to functions on evidence.  In fact, they are really the
    same thing: [->] is just a shorthand for a degenerate use of
    [forall] where there is no dependency, i.e., no need to give a
    name to the type on the LHS of the arrow. *)

Print and_assoc.

(* ===>
        and_assoc = 
        fun (P Q R : Prop) (H : P /\ Q /\ R) => match H with
                                        | conj HP (conj HQ HR) => conj (conj HP HQ) HR
                                        end
                : forall P Q R : Prop, P /\ Q /\ R -> (P /\ Q) /\ R *)


(** When we build a proof using tactics, Coq internally constructs a
    proof object.  We can see how this happens using [Show Proof]: *)

Theorem and_assoc' : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  Show Proof. (* ==> ?Goal *)
  intros P Q R [HP [HQ HR]].
  Show Proof. (* ==> (fun (P Q R : Prop) (H : P /\ Q /\ R) => match H with
                                         | conj HP (conj HQ HR) => ?Goal
                                         end) *)
  split.
  - (* left *) Show Proof. split.
    + (* left *) Show Proof. apply HP.
    + (* right *) Show Proof. apply HQ.
  - (* right *) Show Proof. apply HR.  Show Proof. Qed.



(* ================================================================= *)
(** ** Disjunction *)

Print or.

(* ===>
        Inductive or (A B : Prop) : Prop :=  or_introl : A -> A \/ B | or_intror : B -> A \/ B *)

(** The BHK interpretation: 

A proof of [P \/ Q] is either 
                - a pair [<a, b>] where [a] is [0] and [b] is a proof of [P], or 
                - [a] is [1] and [b] is a proof of [Q]. *)

(** This time, let us reverse the order and discuss _using_ disjunction before discussing how to prove it... *)

(* ----------------------------------------------------------------- *)
(** *** Disjunction: using it *)


(** The corresponding rule can be written in terms of _hypothetical derivations_ with context:

      Gamma |- A \/ B   Gamma , A |- C   Gamma , B |- C  
     ----------------------------------------------------    (\/ E)
                    Gamma |- C

*)


(** 
    To use a disjunctive hypothesis in a proof, we proceed by case
    analysis, which, as for [nat] or other data types, can be done
    with [destruct] or [intros].  Here is an example: *)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  move => ? ? [Hn | Hm];
           by [rewrite Hn | rewrite Hm].
  (* Here's a [Ltac] version ...
  (* This pattern implicitly does case analysis on
     [n = 0 \/ m = 0] *)
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.*)
Qed.

(** We can see in this example that, when we perform case analysis on
    a disjunction [A \/ B], we must satisfy two proof obligations,
    each showing that the conclusion holds under a different
    assumption -- [A] in the first subgoal and [B] in the second.
    Note that the case analysis pattern ([Hn | Hm]) allows us to name
    the hypotheses that are generated in the subgoals. *)

(* ----------------------------------------------------------------- *)
(** *** Disjunction: proving it 
    Conversely, to show that a disjunction holds, we need to show that
    one of its sides does. Two constructors -- two introduction rules! *)

(**

                                Gamma |- A 
                              ----------------------              (\/ I_l)
                                Gamma |- A \/ B

                                Gamma |- B
                             -----------------------              (\/ I_r)
                                Gamma |- A \/ B

*)


(**
    This is done via two tactics, [left] and
    [right].  As their names imply, the first one requires proving the
    left side of the disjunction, while the second requires proving
    its right side. *)

(** Here is a trivial example... *)

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  move => ? ? ?. left. by [].
  (*
  intros A B HA.
  left.
  apply HA.*)
Qed.

(** ... and a slightly more interesting example requiring both [left]
    and [right]: *)

(** We need [Nat] for [pred] ... *)

Require Import Nat.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  move => [|]; by [left|right].
  (*
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.*)
Qed.

Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  (* WORKED IN CLASS *)
  move => [|] ?; first by left.
  case => [|m]; first by right. 
  (* At this stage, [case] would produce a warning "Nothing to inject". In previous versions of [Coq], it actually produced an error: "This equality is discriminable. You should use the discriminate tactic to solve the goal."*)
  discriminate.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  (* WORKED IN CLASS *)
  move => ? ? [|]; by [right | left].
  (*
  intros P Q [HP | HQ].
  - (* left *) right. apply HP.
  - (* right *) left. apply HQ.*)  Qed.

(* ================================================================= *)
(** ** Falsehood and Negation *)

(** So far, we have mostly been concerned with proving that certain
    things are _true_ -- addition is commutative, appending lists is
    associative, etc.  Of course, we may also be interested in
    _negative_ results, showing that certain propositions are _not_
    true. *)

(** In Coq, negative statements are expressed with the
    negation operator [~]. *)

(** 
    To see how negation works, recall the discussion of the _principle
    of explosion_ from the [MoreBasicTactics] chapter; it asserts that, if we
    assume a contradiction, then any other proposition can be derived. *)

(**
    - We could define [~ P] ("not [P]") as [forall Q, P -> Q].  
    - Coq actually makes a slightly different choice, defining [~ P] as [P -> False], where [False] is a
      _particular_ contradictory (empty) proposition defined in the standard library. *)

Print  not.

(* ===>
     not = fun A : Prop => A -> False
     : Prop -> Prop *)

(** What is [False] then ?? *)

Print False.

(** That is, [False] is an inductive type with _no_ constructors --
    i.e., no way to build evidence for it. *)



(** If we get [False] into the proof context, we can destruct it to complete any goal: *)

(**
<< 
           Gamma |-  False
           ----------------------     (False E)
             Gamma |-  P

*)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  move => ? [].
  (*intros P contra.
  destruct contra.*)  Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from falsehood
    follows whatever you like"; this is another common name for the
    principle of explosion. *)

(** In [Ltac], there is, in fact, a tactic for this. *)

Theorem ex_falso_quodlibet' : forall (P:Prop),
  False -> P.
Proof.
   intros ? H. exfalso. apply H.
 Qed.



(** **** Exercise: 2 stars, standard, optional (not_implies_our_not)  

    Show that Coq's definition of negation implies the intuitive one
    mentioned above: *)

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Negation and falsity: proving it *)

(** There is (hopefully!) no way to prove falsity or a contradictory statement in Coq. *)

(** So, no special introduction rule for it. *)

(** But we want to use negation to state _falsity_ of certain sentences, i.e., prove theorems of the form [A -> False]. *)

(** This is how we use [not] to state that [0] and [1] are different
    elements of [nat]: *)

Theorem zero_not_one : ~(0 = 1).
Proof.
  discriminate.
Qed.

(** Such inequality statements are frequent enough to warrant a
    special notation, [x <> y]: *)

Check (0 <> 1).
(* ===> Prop *)

Theorem zero_not_one' : 0 <> 1.
Proof.
  discriminate.
Qed.

(** It takes a little practice to get used to working with negation in
    Coq.  Even though you can see perfectly well why a statement
    involving negation is true, it can be a little tricky at first to
    get things into the right configuration so that Coq can understand
    it!  Here is a proof of a super-easy fact... *)

Theorem not_False :
  ~ False.
Proof.
  by move => [].
Qed.

(** Let us have a quick look at the variety of [Ltac]tics tailored for negation and contradiction. First, a pedestrian proof... *)



Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  move => ? ? [HP HNA].
  apply HNA in HP. by [].
Qed.

(** We have a contradition in contex, so [ssreflect]'s [by] sees immediately what's going on. Actually, it's even quicker than that: *)

Theorem contradiction_implies_anything2 : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  by move => ? ? [? ?].
Qed.

(** But let us return to plain [Ltac]. There's one more [Ltac]tic that comes in handy: [contradiction]. *)

Theorem contradiction_implies_anything3 : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [hp hnp].
  contradiction.
Qed.


(** Yet another strategy is to use [contradict] and then a quick terminator like [assumption] or [done]. *)

Theorem contradiction_implies_anything4 : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [hp hnp].
  contradict hnp. assumption.
Qed.

Theorem contradiction_implies_anything5 : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [hp hnp].
  contradict hnp. done.
Qed.

(** Note we could also rely on good old [exfalso]... *)

Theorem contradiction_implies_anything6 : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [hp hnp].
  exfalso.

  (* Note [assumption] would not work here. *)
  Fail assumption.

  (* [done] is more powerful. *)
  
  done.
Qed.



(** Now use whichever weapon you fancy to kill another famous theorem... *)

(** Note: in the statement of the result below, because of [ssreflect] conventions, we have to be careful how we treat double negation. *)
Theorem double_neg : forall P : Prop,
  P -> ~ ~P.
Proof.
  (* WORKED IN CLASS *)
  by move => ? ? ?.
Qed.



(** Write for yourself a natural deduction proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P]. *)

(** **** Exercise: 2 stars, standard, recommended (contrapositive)  *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)



(* ================================================================= *)
(** ** Equality *)

(** Even Coq's equality relation is not built in.  It has the
    following inductive definition.  (Actually, the definition in the
    standard library is a small variant of this, which gives an
    induction principle that is slightly easier to use.) *)

Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.

Notation "x = y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

(** The way to think about this definition is that, given a set [X],
    it defines a _family_ of propositions "[x] is equal to [y],"
    indexed by pairs of values ([x] and [y]) from [X].  There is just
    one way of constructing evidence for each member of this family:
    applying the constructor [eq_refl] to a type [X] and a value [x :
    X] yields evidence that [x] is equal to [x]. *)

(** The inductive definition of equality corresponds to _Leibniz
    equality_: what we mean when we say "[x] and [y] are equal" is
    that every property on [P] that is true of [x] is also true of
    [y].  *)

Lemma leibniz_equality : forall (X : Type) (x y: X),
  x = y -> forall P:X->Prop, P x -> P y.
Proof.
  (* WORKED IN CLASS *)
  move => ? ? ? [].

  (* Look what happened ... *)

  by [].
Qed.

(** We can use [eq_refl] to construct evidence that, for example, [2 =
    2].  Can we also use it to construct evidence that [1 + 1 = 2]?
    Yes, we can.  Indeed, it is the very same piece of evidence!  The
    reason is that Coq treats as "the same" any two terms that are
    _convertible_ according to a simple set of computation rules.
    These rules, which are similar to those used by [Compute], include
    evaluation of function application, inlining of definitions, and
    simplification of [match]es.  *)

Lemma four: 2 + 2 = 1 + 3.
Proof.
  apply eq_refl.
Qed.

(** The [reflexivity] tactic that we have used to prove equalities up
    to now is essentially just short-hand for [apply refl_equal].

    In tactic-based proofs of equality, the conversion rules are
    normally hidden.  But you can see them
    directly at work in the following explicit proof objects: *)

Definition four' : 2 + 2 = 1 + 3 :=
  eq_refl 4.


End MyEquality.


(* ----------------------------------------------------------------- *)
(** *** Inequality as negation *)

(** Inequality is the negation of equality ... *)

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  move => [] hp; by [].
  (* An old-fashioned [Ltac] proof: 
  intros [] H.
  - (* b = false *)
    unfold not in H.
    exfalso.                (* <=== *)
    apply H. reflexivity.
  - (* b = true *) reflexivity. *)
Qed.

(* ================================================================= *)
(** ** Truth *)

(** Besides [False], Coq's standard library also defines [True], a
    proposition that is trivially true. *)

Print True.

(* ===>
        Inductive True : Prop :=  I : True *)

(** This is incorporating the following axiom:

                ----------------       (True I)
                 Gamma |- True
*)

Lemma True_is_true : True.
Proof. apply I. Qed.

(** Unlike [False], which is used extensively, [True] is used quite
    rarely, since it is trivial (and therefore uninteresting) to prove
    as a goal, and it carries no useful information as a hypothesis.
    But it can be quite useful when defining complex [Prop]s using
    conditionals or as a parameter to higher-order [Prop]s.  We will
    see some examples such uses of [True] later on. *)

(* Sun Jul 14 22:07:53 MSK 2019 *)
