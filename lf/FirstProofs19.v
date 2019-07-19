(** * FirstProofs19: First real proofs in Coq *)

(** Adapted from the Software Foundations for SemProg@FAU 2013--2019 *)

(** Here is how you load material from the previous lecture.
 For the more sophisticated route we follow here, you first need following steps:
  - download the [_CoqProject] file that I posted on StudOn and save it in the same folder
  - write in console

    coq_makefile -Q . LF19 Basics19.v FirstProofs19.v -o Makefile; make


Did not work? A fallback dirty option is to "make clean", rename the "[_CoqProject]" file to something dummy, kill "From LF19" in front of Require, and compile Basics19 manually with coqc. But it's absolute last resort.
  *)

From LF19 Require Export Basics19.

(** Let us also load [ssreflect] again. *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import ssreflect ssrfun ssrbool.



(* ################################################################# *)
(** * Proof by Simplification *)

(** Now that we've defined a few datatypes and functions, let's
    turn to stating and proving properties of their behavior.
    Actually, we've already started doing this: each [Example] in the
    previous sections makes a precise claim about the behavior of some
    function on some particular inputs.

    The same sort of "proof by simplification" can be used to prove
    more interesting properties as well.  For example, the fact that
    [0] is a "neutral element" for [+] on the left can be proved just
    by observing that [0 + n] reduces to [n] no matter what [n] is, a
    fact that can be read directly off the definition of [plus].*)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  reflexivity.  Qed.

(** (You may notice that the above statement looks different in
    the [.v] file in your IDE than it does in the HTML rendition in
    your browser, if you are viewing both. In [.v] files, we write the
    [forall] universal quantifier using the reserved identifier
    "forall."  When the [.v] files are converted to HTML, this gets
    transformed into an upside-down-A symbol.)  *)

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  by []. Qed.

(** It will be useful later to know that [reflexivity]
    does somewhat _more_ simplification than, e.g., [simpl] does -- for
    example, it tries "unfolding" defined terms, replacing them with
    their right-hand sides.  The reason for this difference is that,
    if reflexivity succeeds, the whole goal is finished and we don't
    need to look at whatever expanded expressions [reflexivity] has
    created by all this simplification and unfolding; by contrast,
    [simpl] and its relatives are used in situations where we may have to read and
    understand the new goal that it creates, so we would not want it
    blindly expanding definitions and leaving the goal in a messy
    state.

    The form of the theorem we just stated and its proof are almost
    exactly the same as the simpler examples we saw earlier; there are
    just a few differences.

    First, we've used the keyword [Theorem] instead of [Example].
    As already explained, this difference is purely a matter of style.

    Second, we've added the quantifier [forall n:nat], so that our
    theorem talks about _all_ natural numbers [n].  Informally, to
    prove theorems of this form, we generally start by saying "Suppose
    [n] is some number..."  Formally, this is achieved in the proof by
    [intros n], which moves [n] from the quantifier in the goal to a
    _context_ of current assumptions.

    The keywords [intros], [simpl], and [reflexivity] are examples of
    _tactics_.  A tactic is a command that is used between [Proof] and
    [Qed] to guide the process of checking some claim we are making.
    We will see several more tactics in the rest of this chapter and
    yet more in future chapters.

    Other similar theorems can be proved with the same pattern. *)

Theorem plus_1_l : forall n:nat, 1 + n = S n. by []. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0. reflexivity . Qed.

(** The [_l] suffix in the names of these theorems is
    pronounced "on the left." *)

(**
    Although simplification is powerful enough to prove some fairly
    general facts, there are many statements that cannot be handled by
    simplification alone.  For instance, we cannot use it to prove
    that [0] is also a neutral element for [+] _on the right_. *)

Theorem plus_n_O : forall n, n = n + 0.
Proof.
  intros n.

  Fail reflexivity.

  (** We can finish it in the [ssreflect] way though... *)

  by [].

Qed.

(** We will see another way to deal with this later. *)

(* ################################################################# *)
(** * Proof by Rewriting *)

(** This theorem is a bit more interesting than the others we've
    seen: *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

(** Instead of making a universal claim about all numbers [n] and [m],
    it talks about a more specialized property that only holds when [n
    = m].  The arrow symbol is pronounced "implies."

    As before, we need to be able to reason by assuming we are given such
    numbers [n] and [m].  We also need to assume the hypothesis
    [n = m]. The [intros] tactic will serve to move all three of these
    from the goal into assumptions in the current context.

    Since [n] and [m] are arbitrary numbers, we can't just use
    simplification to prove this theorem.  Instead, we prove it by
    observing that, if we are assuming [n = m], then we can replace
    [n] with [m] in the goal statement and obtain an equality with the
    same expression on both sides.  The tactic that tells Coq to
    perform this replacement is called [rewrite]. *)

Proof.
  (* move both quantifiers and the hypothesis into the context: *)
  intros n m H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity. Qed.

(** The first line of the proof moves the universally quantified
    variables [n] and [m] into the context.  The second moves the
    hypothesis [n = m] into the context and gives it the name [H].
    The third tells Coq to rewrite the current goal ([n + n = m + m])
    by replacing the left side of the equality hypothesis [H] with the
    right side.

    (The arrow symbol in the [rewrite] has nothing to do with
    implication: it tells Coq to apply the rewrite from left to right.
    To rewrite from right to left, you can use [rewrite <-].  Try
    making this change in the above proof and see what difference it
    makes.) *)

(** Here's how to prove this theorem in the [ssreflect] style. *)

Theorem plus_id_example' : forall n m:nat,
  n = m ->
  n + n = m + m.

Proof.
    by
      move => n m H;
               rewrite H. Qed.

(** The use of [move =>] has its advantages, especially regarding
naming conventions. Will discuss it in more detail when we have
a better background later. *)


Theorem plus_id_exercise n m o :
  n = m -> m = o -> n + m = m + o.
Proof.
  by move=> -> ->. Qed.
  (* by move => EQmn EQno; rewrite EQmn EQno. Qed. *)

(** We can also use the [rewrite] tactic with a previously proved
    theorem instead of a hypothesis from the context. If the statement
    of the previously proved theorem involves quantified variables,
    as in the example below, Coq tries to instantiate them
    by matching with the current goal. *)

Theorem mult_double : forall p q : nat,
  p = q -> (p + p) * q = (q + q) * q.
Proof.
  by move => p q EQpq; rewrite EQpq.
Qed.

(** **** Exercise: 2 stars, standard (mult_S_1)  *)
Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
    by move => n m H;
                rewrite H;
                reflexivity.
                Qed.

(* (N.b. This proof can actually be completed without using [rewrite],
   but please do use [rewrite] for the sake of the exercise.)

    [] *)

(* ################################################################# *)
(** * Proof by Case Analysis *)

(** Of course, not everything can be proved by simple
    calculation and rewriting: In general, unknown, hypothetical
    values (arbitrary numbers, booleans, lists, etc.) can block
    simplification.  For example, if we try to prove the following
    fact using the [simpl] tactic as above, we get stuck. *)

Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + 1 =? 0) = false.
Proof.
  intros n.

  Fail reflexivity.
Abort.

(** This time, [ssreflect] finds no magic bullet either... *)

Theorem plus_1_neq_0_firsttry' : forall n : nat,
  (n + 1 =? 0) = false.
Proof.

  move => n.

  Fail by [].

Abort.


(** The reason for this is that the definitions of both
    [beq_nat] and [+] begin by performing a [match] on their first
    argument.  But here, the first argument to [+] is the unknown
    number [n] and the argument to [beq_nat] is the compound
    expression [n + 1]; neither can be simplified.

    To make progress, we need to consider the possible forms of [n]
    separately.  If [n] is [O], then we can calculate the final result
    of [beq_nat (n + 1) 0] and check that it is, indeed, [false].  And
    if [n = S n'] for some [n'], then, although we don't know exactly
    what number [n + 1] yields, we can calculate that, at least, it
    will begin with one [S], and this is enough to calculate that,
    again, [beq_nat (n + 1) 0] will yield [false].

    The tactic that tells Coq to consider, separately, the cases where
    [n = O] and where [n = S n'] is called [destruct]. *)

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1 =? 0) = false.
Proof.
  intros n. Show Proof. destruct n as [| n']. Show Proof.
  - reflexivity.
  - Show Proof. reflexivity.
Qed.


(** There is syntactic sugar for doing [destruct] following [intros]: *)

Theorem plus_1_neq_0' : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [| n'].
   - reflexivity.
   - reflexivity.
Qed.

(** The [destruct] generates _two_ subgoals, which we must then
    prove, separately, in order to get Coq to accept the theorem. The
    annotation "[as [| n']]" is called an _intro pattern_.  It tells
    Coq what variable names to introduce in each subgoal.  In general,
    what goes between the square brackets is a _list of lists_ of
    names, separated by [|].  In this case, the first component is
    empty, since the [O] constructor is nullary (it doesn't have any
    arguments).  The second component gives a single name, [n'], since
    [S] is a unary constructor.

    The [-] signs on the second and third lines are called _bullets_,
    and they mark the parts of the proof that correspond to each
    generated subgoal.  The proof script that comes after a bullet is
    the entire proof for a subgoal.  In this example, each of the
    subgoals is easily proved by a single use of [reflexivity], which
    itself performs some simplification -- e.g., the second one
    simplifies [beq_nat (S n' + 1) 0] to [false] by first rewriting
    [(S n' + 1)] to [S (n' + 1)], then unfolding [beq_nat], and then
    simplifying the [match].

    Marking cases with bullets is entirely optional: if bullets are
    not present, Coq simply asks you to prove each subgoal in
    sequence, one at a time. But it is a good idea to use bullets.
    For one thing, they make the structure of a proof apparent, making
    it more readable. Also, bullets instruct Coq to ensure that a
    subgoal is complete before trying to verify the next one,
    preventing proofs for different subgoals from getting mixed
    up. These issues become especially important in large
    developments, where fragile proofs lead to long debugging
    sessions.

    There are no hard and fast rules for how proofs should be
    formatted in Coq -- in particular, where lines should be broken
    and how sections of the proof should be indented to indicate their
    nested structure.  However, if the places where multiple subgoals
    are generated are marked with explicit bullets at the beginning of
    lines, then the proof will be readable almost no matter what
    choices are made about other aspects of layout.

    This is also a good place to mention one other piece of somewhat
    obvious advice about line lengths.  Beginning Coq users sometimes
    tend to the extremes, either writing each tactic on its own line
    or writing entire proofs on one line.  Good style lies somewhere
    in the middle.  One reasonable convention is to limit yourself to
    80-character lines. *)

(** There is a short way to throw the same tactic on every
    subgoal. It is provided by the [;] _tactical_. "Tacticals"
    are tactics that take other tactics as arguments --
    "higher-order tactics," if you will. We have already seen an
    example of one: it was [by] of [ssreflect]. *)

Theorem plus_1_neq_0'' : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [| n'];  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** The [;] Tactical (General Form) *)

(** The [;] tactical also has a more general form than the simple
    [T;T'] we've seen above.  If [T], [T1], ..., [Tn] are tactics,
    then

      T; [T1 | T2 | ... | Tn]

   is a tactic that first performs [T] and then performs [T1] on the
   first subgoal generated by [T], performs [T2] on the second
   subgoal, etc.

   So [T;T'] is just special notation for the case when all of the
   [Ti]'s are the same tactic -- i.e., [T;T'] is shorthand for:

      T; [T' | T' | ... | T']
*)

(** Again, [ssreflect] provides an even shorter way to split
things by using [case]. *)

Theorem plus_1_neq_0''' : forall n : nat,
  (n + 1 =? 0) = false.
Proof.
    case.
    Abort.

(**
    The [destruct] tactic and its relatives can be used with any inductively defined
    datatype.  For example, we use them next to prove that boolean
    negation is involutive -- i.e., that negation is its own
    inverse. *)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros []; reflexivity .
Qed.

(** ... or, alternatively... *)

Theorem negb_involutive' : forall b : bool,
  negb (negb b) = b.  by case.
Qed.

(** We can have nested subgoals (and we use different "bullets"
    to mark the inner ones): *)

Theorem andb_commutative_boring : forall b c, b && c = c && b.
  destruct b.
  - destruct c.
     + reflexivity.
     + reflexivity.
  - destruct c.
     + reflexivity.
     + reflexivity.
Qed.

(** Better... *)

Theorem andb_commutative : forall b c, b && c = c && b.
Proof.
  intros [] []; reflexivity.
Qed.

(** ... and in the [ssreflect] style ... *)

Theorem andb_commutative' : forall b c, b && c = c && b.
  by do 2! case.
Qed.

Theorem andb_commutative'' : forall b c, b && c = c && b.
  by case; case.
Qed.

Theorem andb_commutative''' b c: b && c = c && b.
  move: b c; by do 2! case.
Qed.

(** Similarly... *)


Theorem andb3_exchange:
  forall b c d, (b && c) && d = (b && d) && c.
Proof.
  intros [] [] []; reflexivity.
Qed.

Theorem andb3_exchange' :
  forall b c d, (b && c) && d = (b && d) && c.
Proof.
    by do 3! case.
Qed.

(* ################################################################# *)
(** * More Exercises *)

(** **** Exercise: 2 stars, standard (identity_fn_applied_twice)

    Use the tactics you have learned so far to prove the following
    theorem about boolean functions. *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
    by move => f H x; rewrite H. Qed.

(** Now state and prove a theorem [negation_fn_applied_twice] similar
    to the previous one but where the second hypothesis says that the
    function [f] has the property that [f x = negb x].*)


Theorem nagation_fn_applied_twice' :
  forall (f : bool -> bool),
    (forall (x: bool), f x = negb x) ->
    forall (b : bool), f (f b) = b.
Proof.
  intros f h x.
  rewrite -> h. rewrite -> h.
  rewrite -> negb_involutive.
  reflexivity.
Qed.

(* With ssreflect *)

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = negb x) ->
    forall (b : bool), f (f b) = b.
Proof.
    by move => f H x;
                rewrite H;
                rewrite H;
                rewrite negb_involutive.
Qed.

(** [] *)


(* ================================================================= *)
(** ** Proof by Induction *)

(** Let us now return to the type of problems we began with:
seemingly trivial reordering making theorem impossible to prove.
*)

Check plus_1_l.

Print Nat.add.

(* Set Printing All. *)
Theorem plus_1_r_attempt : forall n, S n = n + 1.
Proof.
  intros [].
  - reflexivity.
  - Fail reflexivity.
Abort.


(** [ssreflect] also cannot handle examples such as this one
using tactics we've learned so far: *)

Theorem plus_1_r_ssr_attempt : forall n, S n = n + 1.
Proof.
  Fail by [].
  Fail by case.

Abort.

(** ... or such as this one ... *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  Fail by [].
  Fail by case.
Abort.

(** So we're gonna need a bigger boat. *)


(** To prove interesting facts about numbers, lists, and other
    inductively defined sets, we usually need a more powerful
    reasoning principle: _induction_.

    Recall (from high school, a discrete math course, etc.) the
    principle of induction over natural numbers: If [P(n)] is some
    proposition involving a natural number [n] and we want to show
    that [P] holds for _all_ numbers [n], we can reason like this:
         - show that [P(O)] holds;
         - show that, for any [n'], if [P(n')] holds, then so does
           [P(S n')];
         - conclude that [P(n)] holds for all [n].

    In Coq, the steps are the same but the order is backwards: we
    begin with the goal of proving [P(n)] for all [n] and break it
    down (by applying the [induction] tactic) into two separate
    subgoals: first showing [P(O)] and then showing [P(n') -> P(S
    n')].  Here's how this works for the theorem at hand: *)

Theorem plus_n_O_with_ltac : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.
Qed.

(** Like [destruct], the [induction] tactic takes an [as...]
    clause that specifies the names of the variables to be introduced
    in the subgoals.  In the first branch, [n] is replaced by [0] and
    the goal becomes [0 + 0 = 0], which follows by simplification.  In
    the second, [n] is replaced by [S n'] and the assumption [n' + 0 =
    n'] is added to the context (with the name [IHn'], i.e., the
    Induction Hypothesis for [n'] -- notice that this name is
    explicitly chosen in the [as...] clause of the call to [induction]
    rather than letting Coq choose one arbitrarily). The goal in this
    case becomes [(S n') + 0 = S n'], which simplifies to [S (n' + 0)
    = S n'], which in turn follows from [IHn']. *)

(* ----------------------------------------------------------------- *)
(** *** Induction in [ssreflect] *)

(** [ssreflect] avoids the tactic [induction] (along with other
    tactics, like [intro] and [inversion], which we will
    introduce later) since they implement _fragile context
    manipulation heuristics which hinder precise bookkeeping_;
    as you already witnessed, these tactics generate variable
    names on their own, which are possibly referenced later in
    the proof script …

   Instead, the more basic induction tactic [elim] is preferred.
   *)

(* Pro version *)
Theorem plus_1_r n : S n = n + 1.
Proof.
  by elim: n => [| n' /= ->].
Qed.

(* Dumb version 1 *)
Theorem plus_1_r1 n : S n = n + 1.
Proof.
  elim: n => [//| n' H].
  - simpl. rewrite H. reflexivity.
Qed.


(* Dumb version 2 *)
Theorem plus_1_r2 n : S n = n + 1.
Proof.
  elim: n => [//| n' H].
  - simpl. by rewrite H.
Qed.

(* Dumb version 3 *)
Theorem plus_1_r3 n : S n = n + 1.
Proof.
  elim: n => [//| n' H] /=.
  - by rewrite H.
Qed.

(** We see here how on-the-fly simplification is done in
    [ssreflect] (using the switch [/=]). *)


Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
    by elim.
Qed.

Theorem minus_diag' : forall n,
  minus n n = 0.
Proof.
    elim => [//| n].
    - by [].
Qed.

Theorem minus_diag_with_ltac : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(**
    The use of the [intros] tactic in these proofs is actually redundant.
    When applied to a goal that contains quantified variables,
    the [induction] tactic moves them into the context as needed. *)

(* ----------------------------------------------------------------- *)
(** *** More uses of induction *)

(** Prove the following. *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (* WORKED IN CLASS *)
    by elim.
Qed.
(**
Standard Ltac:
[
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.
]
*)

(** Now it's time for associativity. It's slightly more
complicated, but really only slightly so. *)

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  move => n ? ?. (* This is how you do "anonymous intros" in [ssreflect].  *)
  (* WORKED IN CLASS *)
  elim n => [|n' Hn'] /=.
  - by [].
  - by rewrite Hn'.
Qed.

(** Standard Ltac:

    intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.   Qed.
*)

(** How abour commutativity? Here, as it turns out, we need one more little insight... *)

(** Recall our [plus_n_O]? It is not so interesting in its own right. But it's very
    often the case we need such auxiliary lemmas for more interesting
    inductive proofs, such as the one below.  *)

(** First, let us see another lemma already in the standard library... *)

Check plus_n_Sm.

(* =>
plus_n_Sm
     : forall n m : nat, S (n + m) = n + S m *)

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* WORKED IN CLASS *)
  move => n; elim => [|m' IHm'] /=.
  - by rewrite -plus_n_O.
  - by rewrite -IHm' plus_n_Sm.
Qed.
(**
Standard Ltac:

  intros n m. induction m as [| m' IHm'].
  - (* m = 0 *)
    simpl. rewrite <- plus_n_O. reflexivity.
  - (* m = S m' *)
    simpl. rewrite <- IHm'. rewrite <- plus_n_Sm.
    reflexivity.  Qed.
*)





(** **** Exercise: 2 stars, standard, optional (evenb_S)

    One inconveninent aspect of our definition of [evenb n] is that it
    may need to perform a recursive call on [n - 2]. This makes proofs
    about [evenb n] harder when done by induction on [n], since we may
    need an induction hypothesis about [n - 2]. The following lemma
    gives a better characterization of [evenb (S n)]: *)

(* Dumb v1 *)
Theorem evenb_S1 : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  elim.
  - by [].
  - move => n ->.
    rewrite negb_involutive.
    reflexivity.
Qed.

Theorem evenb_S2 : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  by elim => [//| ? ->]; rewrite negb_involutive.
Qed.
(** [] *)



(* ################################################################# *)
(** * Proofs Within Proofs *)

(** In Coq, as in informal mathematics, large proofs are often
    broken into a sequence of theorems, with later proofs referring to
    earlier theorems.  But sometimes a proof will require some
    miscellaneous fact that is too trivial and of too little general
    interest to bother giving it its own top-level name.  In such
    cases, it is convenient to be able to simply state and prove the
    needed "sub-theorem" right at the point where it is used.  The
    [assert] tactic allows us to do this.   *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.

(** The [assert] tactic introduces two sub-goals.  The first is
    the assertion itself; by prefixing it with [H:] we name the
    assertion [H].  (We can also name the assertion with [as] just as
    we did above with [destruct] and [induction], i.e., [assert (0 + n
    = n) as H].)  Note that we surround the proof of this assertion
    with curly braces [{ ... }], both for readability and so that,
    when using Coq interactively, we can see more easily when we have
    finished this sub-proof.  The second goal is the same as the one
    at the point where we invoke [assert] except that, in the context,
    we now have the assumption [H] that [0 + n = n].  That is,
    [assert] generates one subgoal where we must prove the asserted
    fact and a second subgoal where we can use the asserted fact to
    make progress on whatever we were trying to prove in the first
    place. *)

(** The [assert] tactic is handy in many sorts of situations ... *)

(* ----------------------------------------------------------------- *)
(** *** Rewriting guided by assertions *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
    (n + m) + (p + q) = (m + n) + (p + q).

(**
    The only difference between the two sides of the
    [=] is that the arguments [m] and [n] to the first inner [+] are
    swapped, so it seems we should be able to use the commutativity of
    addition ([plus_comm]) to rewrite one into the other.  However,
    the [rewrite] tactic is a little stupid about _where_ it applies
    the rewrite.  There are three uses of [+] here, and it turns out
    that doing [rewrite -> plus_comm] will affect only the _outer_
    one... *)

Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)...
     it seems like plus_comm should do the trick! *)
  rewrite -> plus_comm.
  (* Doesn't work...Coq rewrote the wrong plus! *)
Abort.

(** To get [plus_comm] to apply at the point where we want it to, we
    can introduce a local lemma stating that [n + m = m + n] (for the
    particular [m] and [n] that we are talking about here), prove this
    lemma using [plus_comm], and then use it to do the desired
    rewrite. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Rewriting eased by [ssreflect] *)

(** Introducing a separate assertion just for rewriting purposes can
    quickly become cumbersome. This is another place where [ssreflect]
    shows its strength, namely with its extended [rewrite] tactic:
      - performs rewriting, simplifications, folding/unfolding of definitions
      - can chain rewriting operations
      - enhanced occurrence selection *)

(**
   For example, the proof of [plus_rearrange] above can be shortened
   as follows: *)

Theorem plus_rearrange' : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  move=> n m.
  rewrite [n + _]plus_comm.
  by [].
Qed.

(** The _rewrite pattern_ in square brackets can be (among other
    things not important at this stage) any term. *)

(* ================================================================= *)
(** ** Induction beyond natural numbers *)

(** As you can imagine, we can do induction on any inductive type. Here is one example: *)

(** We can generalize our unary representation of natural numbers to
    the more efficient binary representation by treating a binary
    number as a sequence of constructors [A] and [B] (representing 0s
    and 1s), terminated by a [Z]. For comparison, in the unary
    representation, a number is a sequence of [S]s terminated by an
    [O]. *)

(**
    For example:

        decimal            binary                           unary
           0                   Z                              O
           1                 B Z                            S O
           2              A (B Z)                        S (S O)
           3              B (B Z)                     S (S (S O))
           4           A (A (B Z))                 S (S (S (S O)))
           5           B (A (B Z))              S (S (S (S (S O))))
           6           A (B (B Z))           S (S (S (S (S (S O)))))
           7           B (B (B Z))        S (S (S (S (S (S (S O))))))
           8        A (A (A (B Z)))    S (S (S (S (S (S (S (S O)))))))

    Note that the low-order bit is on the left and the high-order bit
    is on the right -- the opposite of the way binary numbers are
    usually written.  This choice makes them easier to manipulate. *)

Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z    => O
  | A m' => 2 * bin_to_nat m'
  | B m' => 1 + 2 * bin_to_nat m'
  end.

Compute (bin_to_nat Z).
Compute (bin_to_nat (A Z)).
Compute (bin_to_nat (B Z)).
Compute (bin_to_nat (A (B Z))).
Compute (bin_to_nat (B (A (B Z)))).
Compute (bin_to_nat (A (A (B Z)))).
Compute (bin_to_nat (B (A (A (B Z))))).
Compute (bin_to_nat (A (B (A (B Z))))).

(** (a) Complete the definition below of an increment function [incr]
        for binary numbers. *)

Fixpoint incr (m:bin) : bin :=
  match m with
    | Z   => B Z
    | A x => B x
    | B x => A (incr x)
  end.

Example test_bin_incr1 : (incr (B Z)) = A (B Z).
by []. Qed.
Example test_bin_incr2 : (incr (A (B Z))) = B (B Z).
by []. Qed.
Example test_bin_incr3 : bin_to_nat (A (B Z)) = 2.
by []. Qed.
Example test_bin_incr4 :
  bin_to_nat (incr (B Z)) = 1 + bin_to_nat (B Z).
by []. Qed.
Example test_bin_incr5 :
  bin_to_nat (incr (incr (B Z))) = 2 + bin_to_nat (B Z).
by []. Qed.


Theorem incr_is_S m: bin_to_nat (incr m) = S (bin_to_nat m).
Proof.
  elim:m => [//| IHn] /=.
  - by [].
  - move => n ->. by rewrite plus_n_Sm.
Qed.

Print incr_is_S.
Print erefl.

(* Sun Jul 14 22:07:53 MSK 2019 *)
