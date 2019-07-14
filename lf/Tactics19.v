(** * Tactics19: More Basic Tactics *)

(** Adapted from _Software Foundations_  for SemProg@FAU 2013--2019 *)

(** This chapter introduces several additional proof strategies
    and tactics that allow us to begin proving more interesting
    properties of functional programs.  We will see:

    - how to use auxiliary lemmas in both "forward-style" and
      "backward-style" proofs;
    - how to reason about data constructors (in particular, how to use
      the fact that they are injective and disjoint);
    - how to strengthen an induction hypothesis (and when such
      strengthening is required); and
    - more details on how to reason by case analysis. *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import ssreflect ssrbool ssrfun.

(** And instead of our list development in the [Poly19] chapter, let's go for the standard library ... *)

From Coq Require Import List.
Import List.ListNotations.

(** ... and also, for [beq_nat], instead of loading it from [Basics19.v] ... *)

Import Nat.

(** ... and also, for [beq_nat] ... *)

From Coq Require Import Arith.
Notation "x =? y" := (beq_nat x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope. (* [leb] comes from [Nat] *)

(* ================================================================= *)
(** ** The [apply] Tactic *)

(** We often encounter situations where the goal to be proved is
    _exactly_ the same as some hypothesis in the context or some
    previously proved lemma. *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
(** Interlude: Writing an arrow instead of an identifier after a [=>]
    tactical tries to rewrite immediately using the top of the proof
    stack. So the following _anonymously_ introduces the four natural
    numbers, introduces [n = m] temporarily and rewrites the rest of
    the goal with it. *)

  move=> ? ? ? ? <-.

(** Recall the variables introduced anonymously have special names.
    These kinds of names are reserved notation and _cannot_ be used
    any further in the proof. *)

(** Here, we could finish with "[move=> eq. rewrite eq.  by [].]" as we
    have done several times before.  We can achieve the same effect in
    a single step by using the [apply] tactic instead: *)

  by apply. Qed.

(** The [apply] tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  move=> ? ? ? ? eq. apply. apply: eq. Qed.

(** ... and here's [Ltac] style: *)

Theorem silly2' : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  

  (** ... see these confusing names below btw? Before we get here with CoqIDE/Proof General, do you see what they refer to? *)
  
  intros. apply H0. apply H. Qed.



(** You may find it instructive to experiment with this proof
    and see if there is a way to complete it using just [rewrite]
    instead of [apply]. *)

(** Typically, when we use [apply: H], the statement [H] will
    begin with a [forall] that binds some _universal variables_.  When
    Coq matches the current goal against the conclusion of [H], it
    will try to find appropriate values for these variables.  For
    example, when we do [apply: eq2] in the following proof, the
    universal variable [q] in [eq2] gets instantiated with [n] and [r]
    gets instantiated with [m]. *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  move=> n m eq1 eq2. apply: eq2. apply: eq1. Qed.



(** To use the [apply] tactic, the (conclusion of the) fact
    being applied must match the goal exactly -- for example, [apply]
    will not work if the left and right sides of the equality are
    swapped. *)

Theorem silly3_firsttry : forall (n : nat),
     true = (n =? 5)  ->
     (S (S n) =? 7) = true.
Proof.
  move=> n H.

  (** Note btw how [ssreflect] transferred [beq_nat]! *)

  Fail apply H.

(** Here we cannot use [apply] directly, but we can use the [symmetry]
    tactic, which switches the left and right sides of an equality in
    the goal. *)

  symmetry. apply: H. Qed.

(** **** Exercise: 3 stars, standard (rev_exercise1)  

    (_Hint_: You can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [Search] is
    your friend.) *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Just for yourself: briefly explain the difference between the tactics [apply] and
    [rewrite].  What are the situations where both can usefully be
    applied?

(* FILL IN HERE *)
*)

(* ================================================================= *)
(** ** [apply ... with ...] vs. [apply] in [ssreflect] *)

(** The standard library is aware that equality is transitive: *)

Check trans_eq.

(** In [Ltac], applying this lemma to the following example  requires a slight
    variation on [apply]: *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.

  Fail apply trans_eq.
  

(** If we simply tell Coq [apply trans_eq] at this point, it can
    tell (by matching the goal against the conclusion of the lemma)
    that it should instantiate [X] with [[nat]], [n] with [[a,b]], and
    [o] with [[e,f]].  However, the matching process doesn't determine
    an instantiation for [m]: we have to supply one explicitly by
    adding [with (m:=[c,d])] to the invocation of [apply]. *)

  apply trans_eq with (y:=[c;d]).
  apply eq1. apply eq2.   Qed.

(** Actually, we usually don't have to include the name [m] in
    the [with] clause; Coq is often smart enough to figure out which
    instantiation we're giving. We could instead write: [apply
    trans_eq with [c;d]]. *)

(** Here's how to play this in [ssreflect]: *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  move => ? ? ? ? ? ? eq1 eq2.
  apply: trans_eq.

  (* See what happened? *)

  apply: eq1.

  (* ... aaaand we're done *)
  
    by apply: eq2.   Qed.

(** In fact, we can make it even more compact: *)

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  move => ? ? ? ? ? ? eq1 eq2.
  by apply: trans_eq eq1 eq2.
Qed.

(** Let us practice this use of [apply] on the following simple example: *)

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n) => n
  end.


Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  (* WORKED IN CLASS *)
  move=> ? ? ? ? eq1 eq2.
  apply: trans_eq eq2 eq1.
Qed.

(* ================================================================= *)
(** ** Injective and Disjoint Constructors *)

(** Recall the definition of natural numbers:

     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.

    It is obvious from this definition that every number has one of
    two forms: either it is the constructor [O] or it is built by
    applying the constructor [S] to another number.  But there is more
    here than meets the eye: implicit in the definition (and in our
    informal understanding of how datatype declarations work in other
    programming languages) are two more facts:

    - The constructor [S] is _injective_.  That is, if [S n = S m], it
      must be the case that [n = m].

    - The constructors [O] and [S] are _disjoint_.  That is, [O] is not
      equal to [S n] for any [n].

    Similar principles apply to all inductively defined types: all
    constructors are injective, and the values built from distinct
    constructors are never equal.  For lists, the [cons] constructor
    is injective and [nil] is different from every non-empty list.
    For booleans, [true] and [false] are different.  (Since neither
    [true] nor [false] take any arguments, their injectivity is not
    interesting.)  And so on. *)

(** Coq provides tactics called [injection] and [discriminate]
    that allow us to exploit these principles in proofs. To see how to
    use them, let's show explicitly that the [S] constructor is
    injective: *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  move=> n m H.

  injection H.

  (* At this state, we're essentially done. 
   But for the sake of hygiene, let us remove used hypothesis ... *)
  
  clear H.

  (* ... and say goodbye. *)

    by [].
    
Qed.

(** Here's a more interesting example that shows how multiple
    equations can be derived at once. *)

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  move=> n m o H.
  injection H => eq1 eq2.
  by rewrite eq1 eq2.
Qed.

Theorem injection_ex1' : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  move=> n m o.
  case=> eq1 eq2.
  by rewrite eq1 eq2.
Qed.

Example case_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  (* WORKED IN CLASS *)
  move=> X x y z l j eq1 eq2. symmetry.
  by case: eq2. Qed.

Theorem discriminate_ex1 : forall (n m o : nat), S n = O -> m = o.
Proof.
  move=> n m o H.
  discriminate H.
Qed.

Theorem discriminate_ex1' : forall (n m o : nat), S n = O -> m = o.
Proof.
  by [].
Qed.

(** This is an instance of a logical principle known as the _principle
    of explosion_ or, in Latin, _ex falso quodlibet_, which asserts that a contradictory hypothesis
    entails anything, even false things! *)

Theorem explosion_ex4 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof. by []. Qed.

Theorem explosion_ex5 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof. by []. Qed.

(** If you find the principle of explosion confusing, remember
    that these proofs are not actually showing that the conclusion of
    the statement holds.  Rather, they are arguing that, if the
    nonsensical situation described by the premise did somehow arise,
    then the nonsensical conclusion would follow.  We'll explore the
    principle of explosion of more detail in the next chapter. *)

(** To summarize this discussion, suppose [H] is a hypothesis in the
    context or a previously proven lemma of the form [[ c a1 a2 ... an
    = d b1 b2 ... bm ]] for some constructors [c] and [d] and
    arguments [a1 ... an] and [b1 ... bm]. Then:

    - If [c] and [d] are the same constructor, then, by the
      injectivity of this constructor, we know that [a1 = b1], [a2 =
      b2], etc. [case: H] adds these facts to the top of the goal.

    - If [c] and [d] are different constructors, then the hypothesis
      [H] is contradictory, and the current goal doesn't have to be
      considered at all. In this case, [by []] marks the current goal
      as completed. *)

(** [Ltac] has another powerful tactic incorporating these principles. It is called [inversion]. It goes completely against the philosophy you've been seeing in [ssreflect], it's quite messy and can moreover slow down significantly larger proofs. We will avoid it... when we can. But sometimes this big hammer comes really handy. *) 

(** The injectivity of constructors allows us to reason that
    [forall (n m : nat), S n = S m -> n = m].  The converse of this
    implication is an instance of a more general fact about both
    constructors and functions, which we will find useful in a few
    places below: *)

Check f_equal.
Theorem f_equal_reproved : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. by move=> ? ? ? ? ? ->. Qed.

(* ================================================================= *)
(** ** Using Tactics on Hypotheses *)

(** By default, most tactics work on the goal formula and leave
    the context unchanged. However, [ssreflect] has a so-called
    localization tactical called [in], which allows to perform actions
    on the context.

    For example, the tactic [move=> /= in H] performs simplification in
    the hypothesis named [H] in the context. *)

Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b  ->
     n =? m = b.
Proof.
  move=> n m b H. move=> /= in H. by []. Qed.

(** [in] is a powerful and versatile tactical in [ssreflect], but numerous tactics can be combined with [in] also in [Ltac] style: *)

Theorem S_inj' : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b  ->
     n =? m = b.
Proof.
  intros. simpl in H. apply H. Qed.

(**  
  - The ordinary [apply] tactic is a form of "backward
    reasoning" 
  - it says "We're trying to prove [X] and we know [Y->X],
    so if we can prove [Y] we'll be done." 
  - We can apply hypotheses to
    other hypotheses to obtain a form of "forward reasoning" 
  - "We know
    [Y] and we know [Y->X], so we can deduce [X]." *)

Theorem silly3' : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5)  ->
  true = ((S (S n)) =? 7).
Proof.
  move=> n eq H.

  (* Note that the equalities in the hypotheses are oriented
     differently, so let's match them up first. *)

  symmetry in H. symmetry.

  (* Now the conclusion of the hypothesis [eq] lines up with our goal
     and the premise matches [H], so we can _apply_ (in the
     mathematical sense, not the tactic) [H] to [eq] and use [apply]
     to finish. *)

  apply: eq H. Qed.

(** Forward reasoning starts from what is _given_ (premises,
    previously proven theorems) and iteratively draws conclusions from
    them until the goal is reached.  Backward reasoning starts from
    the _goal_, and iteratively reasons about what would imply the
    goal, until premises or previously proven theorems are reached.
    If you've seen informal proofs before (for example, in a math or
    computer science class), they probably used forward reasoning.  In
    general, idiomatic use of Coq tends to favor backward reasoning,
    but in some situations the forward style can be easier to think
    about.  *)

(** There are numerous functions in the standard library that can help you here, such as [Nat.add_succ_r] or [Nat.add_succ_l] ... *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  (* WORKED IN CLASS *)
  elim=> [|n IH m eq] /=; first by case.
  case: m eq => //. (* <- the need to mention eq arises b/c [case] is more controlling than [inversion]... *)
  move=> m' eq. apply: f_equal. apply: IH. move: eq. (* <- see what happened? *)
  rewrite !Nat.add_succ_r !Nat.add_succ_l.
    by case.
Qed.

(* ================================================================= *)
(** ** Varying the Induction Hypothesis *)

(** Here's a function for doubling a natural number: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Sometimes it is important to control the exact form of the
    induction hypothesis when carrying out inductive proofs in Coq.
    In particular, we need to be careful about which of the
    assumptions we move (using [move=>]) from the goal to the context
    before invoking the [elim] tactic.  For example, suppose
    we want to show that the [double] function is injective -- i.e.,
    that it maps different arguments to different results:

    Theorem double_injective: forall n m,
      double n = double m -> n = m.

    The way we _start_ this proof is a bit delicate: if we begin with

      elim.

    all is well.  But if we begin it with

      move=> n m. elim: n.

    we get stuck in the middle of the inductive case... *)


Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  move=> n m. elim: n => [| n IH].
  - (* n = O *) by case: m.
  - (* n = S n' *) case: m IH => [ | m' IH].
    + (* m = O *) by [].
    + (* m = S m' *) move=> eq. apply: f_equal.

(** At this point, the induction hypothesis, [IH], does _not_ give us
    [n = m'] -- there is an extra [S] in the way -- so the goal is
    not provable. *)

      Abort.

(** What went wrong? *)

(** The problem is that, at the point we invoke the induction
    hypothesis, we have already introduced [m] into the context --
    intuitively, we have told Coq, "Let's consider some particular [n]
    and [m]..." and we now have to prove that, if [double n = double
    m] for _these particular_ [n] and [m], then [n = m].

    The next tactic, [elim: n] says to Coq: We are going to show
    the goal by induction on [n].  That is, we are going to prove, for
    _all_ [n], that the proposition

      - [P n] = "if [double n = double m], then [n = m]"

    holds, by showing

      - [P O]

         (i.e., "if [double O = double m] then [O = m]") and

      - [P n -> P (S n)]

        (i.e., "if [double n = double m] then [n = m]" implies "if
        [double (S n) = double m] then [S n = m]").

    If we look closely at the second statement, it is saying something
    rather strange: it says that, for a _particular_ [m], if we know

      - "if [double n = double m] then [n = m]"

    then we can prove

       - "if [double (S n) = double m] then [S n = m]".

    To see why this is strange, let's think of a particular [m] --
    say, [5].  The statement is then saying that, if we know

      - [Q] = "if [double n = 10] then [n = 5]"

    then we can prove

      - [R] = "if [double (S n) = 10] then [S n = 5]".

    But knowing [Q] doesn't give us any help at all with proving
    [R]!  (If we tried to prove [R] from [Q], we would start with
    something like "Suppose [double (S n) = 10]..." but then we'd be
    stuck: knowing that [double (S n)] is [10] tells us nothing about
    whether [double n] is [10], so [Q] is useless.) *)

(** Trying to carry out this proof by induction on [n] when [m] is
    already in the context doesn't work because we are then trying to
    prove a relation involving _every_ [n] but just a _single_ [m]. *)

(** The successful proof of [double_injective] leaves [m] in the goal
    statement at the point where the [induction] tactic is invoked on
    [n]: *)

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  elim=> [| n IHn']; first by case.

(** Notice that both the goal and the induction hypothesis are
    different this time: the goal asks us to prove something more
    general (i.e., to prove the statement for _every_ [m]), but the IH
    is correspondingly more flexible, allowing us to choose any [m] we
    like when we apply the IH. *)

(** Since we are doing a case analysis on [n], we also need a case
    analysis on [m] to keep the two "in sync." *)

(** The 0 case is trivial: *)

    case; first by [].

    (* m = S m' *)
    move=> m' eq.
    apply: f_equal.

(** At this point, since we are in the second branch of the [case],
    the [m'] mentioned in the context is the predecessor of the [m] we
    started out talking about. Since we are also in the [S] branch of
    the induction, this is perfect: if we instantiate the generic [m]
    in the IH with the current [m'] (this instantiation is performed
    automatically by the [apply] in the next step), then [IHn'] gives
    us exactly what we need to finish the proof. *)

    apply: IHn'.
      by case: eq.
Qed.

(** What you should take away from all this is that we need to be
    careful about using induction to try to prove something too
    specific: To prove a property of [n] and [m] by induction on [n],
    it is sometimes important to leave [m] generic. *)

(** The following exercise requires the same pattern. *)

(** **** Exercise: 2 stars, standard (beq_nat_true)  *)
Theorem beq_nat_true : forall n m,
    (n =? m) = true -> n = m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Give a careful informal proof of [beq_nat_true], being as explicit
    as possible about quantifiers. *)

(* FILL IN HERE *)

(** The strategy of doing fewer [move=>] before an [elim] to obtain a
    more general IH doesn't always work by itself; sometimes some
    _rearrangement_ of quantified variables is needed. Suppose, for
    example, that we wanted to prove [double_injective] by induction
    on [m] instead of [n]. *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  move=> n m. elim: m => [| m' IH].
  - (* m = O *) by case: n.
  - (* m = S m' *) case: n IH => [| n' IH].
    + (* n = O *) by [].
    + (* n = S n' *) move=> eq. apply: f_equal.
        (* Stuck again here, just like before. *)
Abort.

(** The problem is that, to do induction on [m], we must first
    introduce [n].  (If we simply say [induction m] without
    introducing anything first, Coq will automatically introduce [n]
    for us!)  *)

(** What can we do about this?  One possibility is to rewrite the
    statement of the lemma so that [m] is quantified before [n].  This
    works, but it's not nice: We don't want to have to twist the
    statements of lemmas to fit the needs of a particular strategy for
    proving them!  Rather we want to state them in the clearest and
    most natural way. *)

(** What we can do instead is to first introduce all the quantified
    variables and then _re-generalize_ one or more of them,
    selectively taking variables out of the context and putting them
    back at the beginning of the goal. The [:] tactical does this... *)

(** ... and, in standard [Ltac], there are several tactics dedicated to this purpose, such as [revert] or [generalize dependendent]. We are not going to discuss the details here. *)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  move=> n m.
  (* [n] and [m] are both in the context *)
  move: m n.
  (* Now [m] and [n] are back in the goal and we can do induction on
     [m] and get a sufficiently general IH. *)
  elim=> [| m' IH].
  - (* m = O *) by case. 
  - (* m = S m' *) case.
    + (* n = O *) by [].
    + (* n = S n' *) move=> n' eq. apply: f_equal.
      apply: IH. by case: eq. Qed.

(** Let's look at an informal proof of this theorem.  Note that
    the proposition we prove by induction leaves [n] quantified,
    corresponding to the use of generalize dependent in our formal
    proof.

    _Theorem_: For any nats [n] and [m], if [double n = double m], then
      [n = m].

    _Proof_: Let [m] be a [nat]. We prove by induction on [m] that, for
      any [n], if [double n = double m] then [n = m].

      - First, suppose [m = 0], and suppose [n] is a number such
        that [double n = double m].  We must show that [n = 0].

        Since [m = 0], by the definition of [double] we have [double n =
        0].  There are two cases to consider for [n].  If [n = 0] we are
        done, since [m = 0 = n], as required.  Otherwise, if [n = S n']
        for some [n'], we derive a contradiction: by the definition of
        [double], we can calculate [double n = S (S (double n'))], but
        this contradicts the assumption that [double n = 0].

      - Second, suppose [m = S m'] and that [n] is again a number such
        that [double n = double m].  We must show that [n = S m'], with
        the induction hypothesis that for every number [s], if [double s =
        double m'] then [s = m'].

        By the fact that [m = S m'] and the definition of [double], we
        have [double n = S (S (double m'))].  There are two cases to
        consider for [n].

        If [n = 0], then by definition [double n = 0], a contradiction.

        Thus, we may assume that [n = S n'] for some [n'], and again by
        the definition of [double] we have [S (S (double n')) =
        S (S (double m'))], which implies by inversion that [double n' =
        double m'].  Instantiating the induction hypothesis with [n'] thus
        allows us to conclude that [n' = m'], and it follows immediately
        that [S n' = S m'].  Since [S n' = n] and [S m' = m], this is just
        what we wanted to show. [] *)

(** Before we close this section and move on to some exercises,
    let's digress briefly and use [beq_nat_true] to prove a similar
    property of identifiers that we may need in later chapters: *)
Inductive id : Type := | Id : nat -> id.
Definition beq_id x y := match x, y with | Id m, Id n => m =? n end.

Theorem beq_id_true : forall x y,
  beq_id x y = true -> x = y.
Proof.
  move=> [m] [n] /= H. rewrite (beq_nat_true m n H). by [].
Qed.


(* ================================================================= *)
(** ** Unfolding Definitions *)

(** It sometimes happens that we need to manually unfold a Definition
    so that we can manipulate its right-hand side.  For example, if we
    define... *)

Definition square n := n * n.

(** ... and try to prove a simple fact about [square]... *)

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  move=> n m /=.

(** ... we get stuck: [/=] doesn't simplify anything at this point,
    and since we haven't proved any other facts about [square], there
    is nothing we can [apply] or [rewrite] with.

    To make progress, we can manually _unfold_ the definition of
    [square] using [ssreflect]'s rewrite tactic: *)

  rewrite /square.

(** There is also the Coq basic tactic [unfold], which basically does
    the same thing, but is less versatile than the extended [rewrite]
    tactic. *)

(** Now we have plenty to work with: both sides of the equality are
    expressions involving multiplication, and we have lots of facts
    about multiplication at our disposal.  In particular, we know that
    it is commutative and associative, and from these facts it is not
    hard to finish the proof. *)

  rewrite -!mult_assoc. (* This is from [Nat] library ... *) 
  rewrite [m*(n*m)]mult_comm.
  by rewrite !mult_assoc.
Qed.

(** At this point, a deeper discussion of unfolding and simplification
    is in order.

    You may already have observed that tacticals like [/=] and [by],
    and the [apply] tactic will often unfold the definitions of
    functions automatically when this allows them to make progress.
    For example, if we define [foo m] to be the constant [5]... *)

Definition foo (x: nat) := 5.

(** then the [by] in the following proof will unfold [foo m] to [(fun x
    => 5) m] and then further simplify this expression to just [5]. *)

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  by [].
Qed.

(** However, this automatic unfolding is rather conservative.  For
    example, if we define a slightly more complicated function
    involving a pattern match... *)

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

(** ...then the analogous proof will get stuck: *)

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  Fail by []. (* Does nothing! *)
Abort.

(** 
 -  Why [by] doesn't make progress here? 
 -  After tentatively unfolding [bar m], it is left with a match
    whose scrutinee, [m], is a variable... 
 -  so the [match] cannot be
    simplified further. 
 -  (It is not smart enough to notice that the two
    branches of the [match] are identical.) 
 -  So it gives up on
    unfolding [bar m] and leaves it alone. 
 -  Similarly, tentatively
    unfolding [bar (m+1)] leaves a [match] whose scrutinee is a
    function application (that, itself, cannot be simplified, even
    after unfolding the definition of [+]), so [simpl] leaves it
    alone. *)

(**

    At this point, there are two ways to make progress. One is to use
    [case] to break the proof into two cases, each focusing on a more
    concrete choice of [m] ([O] vs [S _]). In each case, the [match]
    inside of [bar] can now make progress, and the proof is easy to
    complete. *)

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  by case.
Qed.

(** This approach works, but it depends on our recognizing that the
    [match] hidden inside [bar] is what was preventing us from making
    progress. *)

(** A more straightforward way to make progress is to explicitly tell
    Coq to unfold [bar]. *)

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  move=> m.
  rewrite /bar.

(** Now it is apparent that we are stuck on the [match] expressions on
    both sides of the [=], and we can use [case] to finish the
    proof without thinking too hard. *)

  by case: m.
Qed.

(* ================================================================= *)
(** ** Destructing Compound Expressions *)

(** We have seen many examples where [case] is used to
    perform case analysis of the value of some variable.  But
    sometimes we need to reason by cases on the result of some
    _expression_.  We can also do this with [case].

    Here are some examples: *)

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  move=> n. rewrite /sillyfun.
  case: (n =? 3).
    - (* beq_nat n 3 = true *) by [].
    - (* beq_nat n 3 = false *) case: (n =? 5); by []. Qed.

(** After unfolding [sillyfun] in the above proof, we find that
    we are stuck on [if (beq_nat n 3) then ... else ...].  But either
    [n] is equal to [3] or it isn't, so we can use [case: (beq_nat
    n 3)] to let us reason about the two cases.

    In general, the [case] tactic can be used to perform case
    analysis of the results of arbitrary computations.  If [e] is an
    expression whose type is some inductively defined type [T], then,
    for each constructor [c] of [T], [case: e] generates a subgoal
    in which all occurrences of [e] (in the goal and in the context)
    are replaced by [c]. *)

(* INSTUCTORS: TML19 combine and split exercises moved to HA *)

(** However, [destruct]ing/[case]ing compound expressions requires a bit of care, as
    such [case]s can sometimes provide not enough new information we
    need to complete a proof. 

    For example, suppose we define a function [sillyfun1] like
    this: *)

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

(** Now suppose that we want to convince Coq of the (rather
    obvious) fact that [sillyfun1 n] yields [true] only when [n] is
    odd.  By analogy with the proofs we did with [sillyfun] above, it
    is natural to start the proof like this: *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     odd n = true.
Proof.
  move=> n eq. rewrite /sillyfun1 in eq.
  case: (n =? 3).
  (* stuck... *)
Abort.

(** We get stuck at this point because the context does not
    contain enough information to prove the goal! The problem is that
    we do not obtain equations for the values of [beq_nat n 3] in the
    different branches. Since [beq_nat n 3 = true] in this branch of the
    case analysis, it must be that [n = 3], from which it follows that
    [n] is odd.

    What we would really like is to add an equation to the context
    that records which case we are in. To this end, we can give [case]
    an identifier before the [:] tactical, instructing [ssreflect] to
    generate according equations in the context. *)


(** The [Ltac] way of doing those things is by writing [eqn:]_identifier_ after destructed expression. *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     odd n = true.
Proof.
  move=> n eq. rewrite /sillyfun1 in eq.
  case Heqe3: (n =? 3).
  (* Now we have the same state as at the point where we got
     stuck above, except that the context contains an extra
     equality assumption, which is exactly what we need to
     make progress. *)
    - (* e3 = true *) by rewrite (beq_nat_true _ _  Heqe3).
    - (* e3 = false *)
     (* When we come to the second equality test in the body
        of the function we are reasoning about, we can use
        [beq_nat:] again in the same way, allow us to finish the
        proof. *)
      case Heqe5: (n =? 5).
        + (* e5 = true *)
          by rewrite (beq_nat_true _ _ Heqe5).
        + (* e5 = false *)
          by rewrite Heqe3 Heqe5 in eq.  Qed.

(** **** Exercise: 2 stars, standard (destruct_eqn_practice)  *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)



(* ================================================================= *)
(** ** Review *)

(** We've now seen many of Coq's and [ssreflect]'s most fundamental
    tactics. We'll introduce a few more in the coming chapters, and
    later on we'll see some more powerful _automation_ tactics that
    make Coq help us with low-level details. But basically we've got
    what we need to get work done.

    Here are the ones we've seen:

      - [move=>]: move hypotheses/variables from goal to context

      - [move: x]: move the variable [x] from the context back to an
        explicit hypothesis in the goal formula, if no other
        hypothesis depends on [x]

      - [by []]: finish the proof when it is trivial and reason by
        distinctness of constructors

      - [apply]: prove goal using a hypothesis, lemma, or constructor

      - [... /= ...]: simplify computations

      - [rewrite]: use an equality hypothesis (or lemma) to rewrite
        the goal

      - [... in ...]: rewrite, simplify, etc. in a hypothesis

      - [symmetry]: changes a goal of the form [t=u] into [u=t]

      - [rewrite /...]: replace a defined constant by its right-hand
        side in the goal

      - [case]: case analysis on values of inductively defined types,
        reason by injectivity of constructors

      - [case eqn:...]: specify the name of an equation to be added to
        the context, recording the result of the case analysis

      - [elim]: induction on values of inductively defined types

      - [assert (H: e)] (or [assert (e) as H]): introduce a "local
        lemma" [e] and call it [H] *)

(* ================================================================= *)
(** ** Standard Coq alternatives *)

(** Of course, all the tasks we dealt with in
    this chapter can be done without [ssreflect] using basic Coq
    tactics.

    Remember though that the standard Coq tactics
    in many cases implement fragile heuristics for name generation and
    context manipulation, which can make proof scripts a lot harder to
    read and understand.

    For completeness, here is a list of alternative tactics (not)
    covered in this chapter:

      - [apply ... in ...]: "forward reasoning" by applying inside
        hypotheses

      - [destruct]: alternative to [case] for compound expressions;
        substitutes the term to destruct in the goal and the whole
        context (fragile!)

      - [inversion]: alternative to [case] for injective constructors
        and discriminable equations; introduces equations in the
        context, generating names for them automatically (fragile!)

      - [generalize dependent]: alternative to [move:], but moves
        items in the context dependent on the variable to be
        generalised into the goal as well. *)


(* ================================================================= *)
(** ** Micro Sermon *)

(** Mindless proof-hacking is a terrible temptation...

    Try to resist! *)

(* ================================================================= *)
(** ** Additional Exercises *)

(** TODO TODO TODO CR2017 **)

(** **** Exercise: 3 stars, standard (beq_nat_sym)  *)
Theorem beq_nat_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (beq_nat_trans)  *)
Theorem beq_nat_trans : forall n m p,
  (n =? m) = true ->
  (m =? p) = true ->
  (n =? p) = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (filter_exercise)  

    This one is a bit challenging.  Pay attention to the form of your
    induction hypothesis. *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Define two recursive [Fixpoints], [forallb] and [existsb].  The
    first checks whether every element in a list satisfies a given
    predicate:

      forallb odd [1;3;5;7;9] = true

      forallb negb [false;false] = true

      forallb even [0;2;4;5] = false

      forallb (beq_nat 5) [] = true

    The second checks whether there exists an element in the list that
    satisfies a given predicate:

      existsb (beq_nat 5) [0;2;3;6] = false

      existsb (andb true) [true;true;false] = true

      existsb odd [1;0;0;0;0;3] = true

      existsb even [] = false

    Next, define a _nonrecursive_ version of [existsb] -- call it
    [existsb'] -- using [forallb] and [negb].

    Finally, prove a theorem [existsb_existsb'] stating that
    [existsb'] and [existsb] have the same behavior. *)

(* FILL IN HERE *)

(** $Date: 2017-06-06 14:19:57 +0200 (Tue, 06 Jun 2017) $ *)


(* Sun Jul 14 22:07:53 MSK 2019 *)
