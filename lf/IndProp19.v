(** * IndProp19: Inductively Defined Propositions *)

(** Adapted from _Software Foundations_  for SemProg@FAU 2013--2019 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import ssreflect ssrbool ssrfun.

Require Import PeanoNat. (* for basic properties of [nat] functions! *)
Import Nat.



(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** We have already looked at several ways of writing propositions,
    including conjunction, disjunction, and quantifiers. Now we need to examine
    _inductive definitions_ in some detail.

    Recall that we have seen two ways of stating that a number [n] is even: We
    can say (1) [even n = true], or (2) [exists k, n = double k]. Yet another
    possibility is to say that [n] is even if we can establish its evenness from
    the following rules:

       - Rule [ev_0]: The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even.

    To illustrate how this new definition of evenness works, let's use its rules
    to show that [4] is even. By rule [ev_SS], it suffices to show that [2] is
    even. This, in turn, is again guaranteed by rule [ev_SS], as long as we can
    show that [0] is even. But this last fact follows directly from the [ev_0]
    rule. *)

(**  Such definitions are often presented using inference rules, just like with logical connectives themselves: 

                              ------------                        (ev_0)
                                 ev 0

                                  ev n
                             --------------                      (ev_SS)
                              ev (S (S n))

*)

(** Each of the textual rules above is reformatted here as an inference
    rule; the intended reading is that, if the _premises_ above the line all
    hold, then the _conclusion_ below the line follows. For example, the rule
    [ev_SS] says that, if [n] satisfies [ev], then [S (S n)] also does. If a
    rule has no premises above the line, then its conclusion holds
    unconditionally.

    We can represent a proof using these rules by combining rule applications
    into a proof tree. Here's how we might transcribe the above proof that [4]
    is even: 

                ------  (ev_0)
                 ev 0
                ------ (ev_SS)
                 ev 2
                ------ (ev_SS)
                 ev 4

    Why call this a "tree" (rather than a "stack", for example)?
    Because, in general, inference rules can have multiple premises.
    We will see examples of this below. *)

(** Putting all of this together, we can translate the definition of
    evenness into a formal Coq definition using an [Inductive]
    declaration, where each constructor corresponds to an inference
    rule: *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

(** This definition is different in one crucial respect from
    previous uses of [Inductive]: its result is not a [Type], but
    rather a function from [nat] to [Prop] -- that is, a property of
    numbers.  Note that we've already seen other inductive definitions
    that result in functions, such as [list], whose type is [Type ->
    Type].  What is new here is that, because the [nat] argument of
    [ev] appears _unnamed_, to the _right_ of the colon, it is allowed
    to take different values in the types of different constructors:
    [0] in the type of [ev_0] and [S (S n)] in the type of [ev_SS].

    In contrast, the definition of [list] names the [X] parameter
    _globally_, to the _left_ of the colon, forcing the result of
    [nil] and [cons] to be the same ([list X]). *)

(**
    Had we tried to bring
    [nat] to the left in defining [ev], we would have seen an error:
    *)

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : forall n, wrong_ev n -> wrong_ev (S (S n)).
(* ===> Error: A parameter of an inductive type n is not
        allowed to be used as a bound variable in the type
        of its constructor. *)

(** ("Parameter" here is Coq jargon for an argument on the left of the
    colon in an [Inductive] definition; "index" is used to refer to
    arguments on the right of the colon.) *)

(** We can think of the definition of [ev] as defining a Coq property
    [ev : nat -> Prop], together with theorems [ev_0 : ev 0] and
    [ev_SS : forall n, ev n -> ev (S (S n))].  Such "constructor
    theorems" have the same status as proven theorems.  In particular,
    we can use Coq's [apply] tactic with the rule names to prove [ev]
    for particular numbers... *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax: *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** We can also prove theorems that have hypotheses involving [ev]. *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  move => n Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(* ================================================================= *)
(** ** Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _reason about_ such evidence.

    Introducing [ev] with an [Inductive] declaration tells Coq not only that the
    constructors [ev_0] and [ev_SS] are valid ways to build evidence that some
    number is even, but also that these two constructors are the _only_ ways to
    build evidence that numbers are even (in the sense of [ev]). *)

(** In other words, if someone gives us evidence [E] for the assertion
    [ev n], then we know that [E] must have one of two shapes:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [ev n']). *)

(** This suggests that it should be possible to analyze a hypothesis
    of the form [ev n] much as we do inductively defined data
    structures; in particular, it should be possible to argue by
    _induction_ and _case analysis_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(** Subtracting two from an even number yields another even number. We can
    easily prove this claim with the techniques that we've already seen,
    provided that we phrase it in the right way. If we state it in terms of
    [even] (defined in the Nat standard library), for instance, we can proceed
    by a simple case analysis on [n]: *)


Theorem even_minus2: forall n,
  even n = true -> even (pred (pred n)) = true.
Proof.
  by move => [ | [ | n' ] ].
Qed.


(** We can state the same claim in terms of [ev], but this quickly
    leads us to an obstacle: Since [ev] is defined inductively --
    rather than as a function -- Coq doesn't know how to simplify a
    goal involving [ev n] after case analysis on [n]... *)

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof.
  move => [ | [ | n' ] ].
  - (* n = 0 *) move => ?; by apply ev_0.
  - (* n = 1 *) move => ?; by apply ev_0.
    -  (* n = n' + 2 *) move => /= ?.  (* what now though? *)
Abort.

(** The solution is to perform case analysis on the evidence that [ev n]
    _directly_. By the definition of [ev], there are two cases to consider:

    - If that evidence is of the form [ev_0], we know that [n = 0]. Therefore,
      it suffices to show that [ev (predn (predn 0))] holds. By the definition
      of [predn], this is equivalent to showing that [ev 0] holds, which
      directly follows from [ev_0].

    - Otherwise, that evidence must have the form [ev_SS n' E'], where [n = S (S
      n')] and [E'] is evidence for [ev n']. We must then show that [ev (predn
      (predn (S (S n'))))] holds, which, after simplification, follows directly
      from [E']. *)

(** Here is how it's done formally: *)

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  move => n [| n' E'].
  - (* E = ev_0 *) by apply ev_0.
  - (* E = ev_SS n' E' *) by  apply E'.  Qed.

(** There are, however, more problematic  instances. Here's one: *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  move => n  [ | n' E'].
 (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
Abort.

(** What happened, exactly? Destructing the evidence has the effect of
    replacing all occurrences of the property argument by the values that
    correspond to each constructor. This is enough in the case of [ev_minus2']
    because that argument, [n], is mentioned directly in the final goal.
    However, it doesn't help in the case of [evSS_ev] since the term that gets
    replaced, i.e., ([S (S n)]) is not mentioned anywhere. *)

(** In standard [Ltac], the tactic used in such cases is [inversion], which can
    detect 
    - (1) that the first case does not apply, and 
    - (2) that the [n'] that appears on the [ev_SS] case must be the same as [n]. *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  move => n E.
  inversion E as [| n' E'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** But, as stated on several previous occasions, [ssreflect] avoids the use of
    [inversion] by design. In fact, we have arrived at a point where a more
    systematic discussion of principles underlying [ssreflect] is necessary... *)


(* ================================================================= *)
(** ** Full Syntax of Case Distinction *)

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  move => n E.

    
  (**
   -  Recall that [inversion] on [E] pulled new equations out of the hat
      by inspecting the assumption and applying some heuristics. 
   -  In [ssreflect],
      we would like to do that in a more coordinated way. 
   -  We want to do case
      distinction on the constructors of [E], instantiating them with [S (S n)] as
      their parameter. 
   -  This can be done using the [case: ... / ...] variant of
      the [case] tactic. 
   -  Note that for example [ case E' :  (S n) / E] results in error: "the given pattern matches the term (S n) while the inferred pattern (S (S n)) doesn't" *)

  Fail  case E' :  (S n) / E.

  (** But it works with a matching pattern: *) 
  
  case E' : (S (S n)) / E.

  
    (** We could write [case E' : (S (S n)) / E => [|n' en']] to give names to things. *)

(** We could also let ssreflect infer the obvious pattern by using underscore. *)

  
    (** The [case] tactic now creates a subgoal for the constructor [ev_0],
      trying to match its parameter (the constant [0]) with the supplied pattern
      [S (S n)]. We used the equation generation feature to give the name [E'] to
      this equation, which is obviously discriminable: *)

  - by [].

    (** The second case creates a subgoal for [ev_SS]. It matches the
      parameter of the conclusioin of the constructor ([ev S (S n)]) with our
      supplied pattern and introduces its premises into the context. Of course,
      it chooses a new name for the natural number [n]; this is done anonymously
      here, but we could write [case E' : (S (S n)) / E => [|n']] to give it a name,
      if we wanted to reuse it later in the proof. This is not necessary here,
      we can just perform case distinction on [E'] to strip the constructors off
      the two numbers and rewrite with the resulting equation to solve the goal.
      *)

  - by case: E' => -> .

Qed.
    

(** By using this methodology, we can also apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductive properties. For
    example: *)

Theorem one_not_even : ~ ev 1.
Proof.
  by case E : _ /. Qed.

(** Prove the following results using [case: ... / ...]. *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* WORKED IN CLASS *)
  move=> n.
  case E :_ / => [|n' H] //.
  (*case E : (S (S (S (S n)))) / => [|n' H] //.*)
  case: _/H E => [|? ?] //.
  by case=> ->. Qed.







(** An even simpler theorem: *)

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  case E1: _ / => [| n Hn] //. 
  case E2: _ / Hn => [|n' Hn'] //; rewrite E2 in E1.
  (* WORKED IN CLASS *)
  - discriminate.
  - case E3: _ / Hn' => [|n'' Hn'']; rewrite E3 in E1.
    + discriminate.
    + by case n.
Qed.      
 









(** This look repetive. Let us smoothen this up a bit: *)

Theorem even5_nonsense' :
  ev 5 -> 2 + 2 = 9.
Proof.
  (*case E1: 5 / => [| n Hn] //. 
  case E2: _ / Hn => [|n' Hn'] *)
  case E1: _ / => [| n Hn] //.
  case: E1 Hn => <-. (* Automating further: *)
  
   (* WORKED IN CLASS *)
  case E1: _ / => [| n' Hn] //.
  case: E1 Hn => <-.  
  case E1: _ / => [| n'' Hn] //.
Qed.
 
(** But this looks repetitive too. If we don't insist on naming the number and use the [do] tactical, we can finally reach perfection ... *)





(** Here we go! *)



Theorem even5_nonsense'' :
  ev 5 -> 2 + 2 = 9.
Proof.
  do 3!(case E1: _ / => [| ? Hn] //;
  case: E1 Hn => <-).
Qed.

(* ================================================================= *)
(** ** Boolean Reflection *)

Import Nat.

(** Before we go on, we need to prove some intermediate facts about
    evenness. *)

Theorem even_S : forall n : nat, even (S n) = ~~ (even n).
Proof.
  elim=> /= [|n IH].
  - by [].
  - by rewrite IH; case: (even n).
Qed.

(** The next fact states that we can represent any natural number in terms
    of the double function. *)

Theorem even_double_conv : forall n, exists k, n = if even n then double k else (S (double k)).
Proof.
  (** Hint: using the lemma above and destructing compound expressions might help. 
      Also, standard library lemmas about adding successor... *)
  (* WORKED IN CLASS *)
  elim=>  [|n [n' Heq]]; first by exists 0.
  rewrite even_S.
  case : (even n) Heq => /= ->; [by exists n' | exists (S n')]. 
  by rewrite /double -add_succ_r -add_succ_l.
Qed.  

Theorem ev_double : forall n,
  ev (double n).
Proof.
  (* WORKED IN CLASS *)
  elim=> [| n' Hn]; first by apply ev_0.
  rewrite /double [(S n') + (S n')]add_succ_r add_succ_l. apply ev_SS. apply Hn. Qed.

(** We have already witnessed that there is an obvious distinction between
    boolean values and elements of Prop. Logical connectives in Prop are
    _types_, giving information about the structure of their proofs. [bool] is a
    _datatype_, logical connectives are just functions, defined by their truth
    tables. 

    Proofs about propositions in [bool], as we have seen, are often simple
    applications of [case]: *)

Lemma b_or_not_b : forall b : bool, b || ~~b = true.
Proof. by case. Qed.

(** Thus, [Prop] and [bool] are complementary: [Prop] allows robust natural
    deduction, [bool] allows brute-force evaluation.

    Coq automatically coerces booleans into propositions using the _coercion_
    mechanism: *)

(* Coercion is_true (b : bool) := b = true. *)
Check is_true. (* => Bool -> Prop *)

(** Coercions require some care... they can lead to some serious confusions with output and pretty printing!  *)

Print reflect.
(* ==> 
   Inductive reflect (P : Prop) : bool -> Set :=
       ReflectT : P -> reflect P true
     | ReflectF : ~ P -> reflect P false *)

(** The statement (reflect P b) asserts that (is_true b) and P are logically
    equivalent propositions. *)

(** Let us look at the most simple evidence for [reflect]: *)

Check idP.
Lemma idP' : forall b : bool, reflect b b.
  Proof. by case; [left | right]. Qed.

(** Notice that the first [b] in [reflect b b] is actually the proposition
    [is_true b]! *)

(** This is actually part of the [ssreflect] libraries, together with another
    important candidate: *)

Check iffP.
Lemma iffP' : forall (P Q : Prop) (b : bool),
    reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b.
Proof.
  move=> P Q b. case; move=> p PQ QP.
  by left; apply (PQ p).
  by right; move=> q; have F := QP q.
Qed.

(** In other words, we can relate two propositions with the same boolean if we
    give a biimplication between the propositions. *)

(** Now we can state our first so-called _reflection view_, a lemma witnessing
    the equivalence between a proposition and a boolean: *)

Lemma evenP : forall n : nat, reflect (exists k, n = double k) (even n).
Proof.
  move=> n.
  apply: (iffP idP).
  - move=> H.
    case: (even_double_conv n) => [k Hk].
    by rewrite Hk H; exists k.
  - move=> [k Hk]. rewrite {}Hk.
    elim: k => [|k IHk] => //.
    by rewrite /double [(S k) + _]add_succ_r add_succ_l; apply: IHk.
Qed. 

(** We will learn how to use it efficiently now. *)

(* ================================================================= *)
(** ** Induction on Evidence *)

(** The earlier [ev_double] exercise shows that our new notion
    of evenness is implied by the two earlier ones. To show that all three
    coincide, we just need the following lemma: *)
    
Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  move=> n E.

(** We are now supposed to provide a witness of a Prop for which we have
    just defined a _reflection view_. Thus, we can use [ssreflect]'s syntax
    [apply/...] to interpret the goal as a boolean proposition: *)

  apply/evenP.

(** We could try to proceed by case analysis or induction on [n]. But
    since [ev] is mentioned in a premise, this strategy would probably lead to a
    dead end, as in the previous section. Thus, it seems better to first try
    [case] on the evidence for [ev]. Indeed, the first case can be solved
    trivially. *)
  
  case H: _ / E => [|n' E'] => //.

(** Unfortunately, the second case is harder. We need to show [even
    (S (S n'))], but the only available assumption is [E'], which states that [ev n']
    holds. Since this isn't directly useful, it seems that we are stuck and that
    performing case analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see that
    something interesting happened: By performing case analysis on [E], we were
    able to reduce the original result to an similar one that involves a
    _different_ piece of evidence for [ev]: [E']. More formally, we can finish
    our proof by showing that [[ even n' ]] which is the same as
    the original statement, but with [n'] instead of [n]. Indeed, it is not
    difficult to convince Coq that this intermediate result suffices. *)

    move => /=.

(** If this looks familiar, it is no coincidence: We've encountered
    similar problems in the [Induction] chapter, when trying to use
    case analysis to prove results that required induction.  And once
    again the solution is... induction! *)

(** This time, however, it's induction on evidence. *)

      by elim E'.

(** Any idea why it was possible to finish the job so quickly? *)
      
Qed.

Lemma ev_even' : forall n,
  ev n -> exists k, n = double k.
Proof.
  move=> n E.
  apply/evenP.
  elim: E => [|n' E' IH]; first by [].

(** Here, we can see that Coq produced an [IH] that corresponds to [E'],
    the single recursive occurrence of [ev] in its own definition. Since [E']
    mentions [n'], the induction hypothesis talks about [n'], as opposed to [n]
    or some other number. *)

  by [].
Qed.

(** As we will see later, induction on evidence is a
    recurring technique when studying the semantics of programming
    languages, where many properties of interest are defined
    inductively. *)

(** The equivalence between the second and third definitions of evenness now
    follows. In other words, we can easily add a reflection view for [ev n] as
    well. *)

Lemma evP : forall n : nat, reflect (ev n) (even n).
Proof.
  move=>n.
  apply/(iffP idP).
  - move/evenP.
    move=> [k Hk].
    rewrite Hk.
    by apply ev_double.
  - move=> ?.
    apply/evenP.
    by apply: ev_even.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** **** Exercise: 2 stars, standard (ev_even_iff)  *)
Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (ev_sum)  *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* Sun Jul 14 22:07:54 MSK 2019 *)
