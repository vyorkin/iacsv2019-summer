(** ** ToyImpArBool19: Perversely simple arithmetical expressions *) 

(** Adapted for SemProg@FAU 2013--2019 *)

(** 
  - We begin a new direction that will continue for
    the rest of the course.
  - Up to now most of our attention has been
    focused on various aspects of Coq itself, while from now on we'll
    mostly be using Coq to formalize other things.  (We'll continue to
    pause from time to time to introduce a few additional aspects of  Coq and [ssreflect].)
  - From the next lecture on, we might even start a separate folder for that.
  - Our first case study is a _simple imperative programming language_
    called Imp, embodying a tiny core fragment of conventional
    mainstream languages such as C and Java. *)

(**
 Here is a familiar
    mathematical function written in Imp.

     Z ::= X;;
     Y ::= 1;;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END


*)

(** This chapter looks at how to define the _syntax_ and _semantics_
    of Imp; the chapters that follow develop a theory of _program
    equivalence_ and introduce _Hoare Logic_, a widely used logic for
    reasoning about imperative programs. 

    Today, we'll only do arithmetic and boolean subexpressions, commands have to wait for the next week. *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import ssreflect ssrbool ssrfun.

From Coq Require Import List.
Import List.ListNotations.

(*Require Import Coq.Bool.Bool.*)
From Coq Require Import Arith.
Import Arith.EqNat. (** This is where "=?" comes from *)




(* ================================================================= *)
(** ** Arithmetic and Boolean Expressions *)

(** We'll present Imp in three parts: first a core language of
    _arithmetic and boolean expressions_, then an extension of these
    expressions with _variables_, and finally a language of _commands_
    including assignment, conditions, sequencing, and loops. *)

(** Some notions and ideas I assume you might have heard about:
        - structure of an interpreter, 
        - the processes of lexing and parsing, 
        - the notion of ASTs (Abstract Syntax Trees)... *)

(** So, the good news is that we're starting to have fun. The bad news, as I said,
    is that actual commands will have to wait for the next lecture. *)

(* ================================================================= *)
(** ** Syntax *)

(** These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(** In this chapter, we'll elide the translation from the
    concrete syntax that a programmer would actually write to these
    abstract syntax trees -- the process that, for example, would
    translate the string ["1+2*3"] to the AST [APlus (ANum
    1) (AMult (ANum 2) (ANum 3))].  The optional chapter [ImpParser]
    develops a simple implementation of a lexical analyzer and parser
    that can perform this translation.  You do _not_ need to
    understand that chapter to understand this one, but if you haven't
    taken a course where these techniques are covered (e.g., a
    compilers course) you may want to skim it. *)

(** For comparison, here's a conventional BNF (Backus-Naur Form)
    grammar defining the same abstract syntax:

    a ::= nat
        | a + a
        | a - a
        | a * a

    b ::= true
        | false
        | a = a
        | a <= a
        | not b
        | b and b
*)

(** Compared to the Coq version above...

       - The BNF is more informal -- for example, it gives some
         suggestions about the surface syntax of expressions (like the
         fact that the addition operation is written [+] and is an
         infix symbol) while leaving other aspects of lexical analysis
         and parsing (like the relative precedence of [+], [-], and
         [*], the use of parens to explicitly group subexpressions,
         etc.) unspecified.  Some additional information (and human
         intelligence) would be required to turn this description into
         a formal definition, for example when implementing a
         compiler.

         The Coq version consistently omits all this information and
         concentrates on the abstract syntax only.

       - On the other hand, the BNF version is lighter and easier to
         read.  Its informality makes it flexible, which is a huge
         advantage in situations like discussions at the blackboard,
         where conveying general ideas is more important than getting
         every detail nailed down precisely.

         Indeed, there are dozens of BNF-like notations and people
         switch freely among them, usually without bothering to say
         which form of BNF they're using because there is no need to:
         a rough-and-ready informal understanding is all that's
         important. *)

(** It's good to be comfortable with both sorts of notations:
    informal ones for communicating between humans and formal ones for
    carrying out implementations and proofs. *)

(* ================================================================= *)
(** ** Evaluation *)

(** _Evaluating_ an arithmetic expression produces a number. *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum     n   => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. by []. Qed.

(** Similarly, evaluating a boolean expression yields a boolean. *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BNot b1     => ~~(beval b1)
  | BAnd b1 b2  => (beval b1) && (beval b2)
  end.

(* ================================================================= *)
(** ** Optimization *)

(** We haven't defined very much yet, but we can already get
    some mileage out of the definitions.  Suppose we define a function
    that takes an arithmetic expression and slightly simplifies it,
    changing every occurrence of [0+e] (i.e., [(APlus (ANum 0) e])
    into just [e]. *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

(** To make sure our optimization is doing the right thing we
    can test it on some examples and see if the output looks OK. *)

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. by []. Qed.

(** But if we want to be sure the optimization is _correct_ --
    i.e., that evaluating an optimized expression gives the same
    result as the original -- we should prove it. *)

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  elim.
  - (* ANum *) by [].
  - (* APlus *) case.
    + (* a1 = ANum n *) case.
      * (* n = 0 *)  by [].
      * (* n <> 0 *) by move=> /= n _ a ->.
    + (* a1 = APlus a2 a3 *) by move=> /= a1 a2 -> a3 ->.
    + (* a1 = AMinus a2 a3 *) by move=> /= a1 a2 -> a3 ->.
    + (* a1 = AMult a2 a3 *) by move=> /= a1 a2 -> a3 ->.
  - (* AMinus *) by move=> /= a1 -> a2 ->.
  - (* AMult *) by move=> /= a1 -> a2 ->. Qed.

(* ================================================================= *)
(** ** Coq Automation *)

(** The repetition in this last proof is starting to be a little
    annoying.  If either the language of arithmetic expressions or the
    optimization being proved sound were significantly more complex,
    it would begin to be a real problem.

    So far, we've been doing all our proofs using just a small handful
    of Coq's tactics and completely ignoring its powerful facilities
    for constructing parts of proofs automatically.  This section
    introduces some of these facilities, and we will see more over the
    next several chapters.  Getting used to them will take some
    energy -- Coq's automation is a power tool -- but it will allow us
    to scale up our efforts to more complex definitions and more
    interesting properties without becoming overwhelmed by boring,
    repetitive, low-level details. *)

(* ================================================================= *)
(** ** Tacticals *)

(** _Tacticals_ is Coq's term for tactics that take other tactics as
    arguments -- "higher-order tactics" if you will.  *)

(** "_I had an impulse 
to clear it all away 
Oh I used the tactics--make everybody pay.  
Just something that I knew I had to do_."  --Joy Division *)

(* ----------------------------------------------------------------- *)
(** *** The [try] Tactical *)

(** If [T] is a tactic, then [try T] is a tactic that is just like [T]
    except that, if [T] fails, [try T] _successfully_ does nothing at
    all (instead of failing). *)

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. (* this just does [reflexivity] *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  move=> P HP.
  try reflexivity. (* just [reflexivity] would have failed *)
  by []. (* we can still finish the proof in some other way *)
Qed.

(** There is no real reason to use [try] in completely manual
    proofs like these, but we'll see below that it is very useful for
    doing automated proofs in conjunction with the [;] tactical. *)

(** Using [try] and [;] together, we can get rid of the repetition in
    the proof that was bothering us a little while ago. *)

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  elim;
    (* Most cases follow directly by the IH... *)
    try (by move=> /= a -> a1 ->).
    (* ... but the remaining cases -- ANum and APlus -- 
       are different: *)
  - (* ANum *) by [].
  - (* APlus *)
    case;
      (* Again, most cases follow directly by the IH: *)
      try (by move=> /= a1 a2 -> a3 ->).
    (* The interesting case, on which the [try...]
       does nothing, is when [e1 = ANum n]. In this
       case, we have to destruct [n] (to see whether
       the optimization applies) and rewrite with the
       induction hypothesis. *)
    + (* a1 = ANum n *) by case => [| n]; move=> /= _ a ->.
Qed.

(** Coq experts often use this "[...; try... ]" idiom after a tactic
    like [elim] to take care of many similar cases all at once.
    Naturally, this practice has an analog in informal proofs.

    Here is an informal proof of this theorem that matches the
    structure of the formal one:

    _Theorem_: For all arithmetic expressions [a],

       aeval (optimize_0plus a) = aeval a.

    _Proof_: By induction on [a].  Most cases follow directly from the IH.  
    The remaining cases are as follows: 

      - Suppose [a = ANum n] for some [n].  We must show

          aeval (optimize_0plus (ANum n)) = aeval (ANum n).

        This is immediate from the definition of [optimize_0plus].

      - Suppose [a = APlus a1 a2] for some [a1] and [a2].  We
        must show

          aeval (optimize_0plus (APlus a1 a2))
        = aeval (APlus a1 a2).

        Consider the possible forms of [a1].  For most of them,
        [optimize_0plus] simply calls itself recursively for the
        subexpressions and rebuilds a new expression of the same form
        as [a1]; in these cases, the result follows directly from the
        IH.

        The interesting case is when [a1 = ANum n] for some [n].
        If [n = ANum 0], then

          optimize_0plus (APlus a1 a2) = optimize_0plus a2

        and the IH for [a2] is exactly what we need.  On the other
        hand, if [n = S n'] for some [n'], then again [optimize_0plus]
        simply calls itself recursively, and the result follows from
        the IH.  [] *)

(** This proof can still be improved: the first case (for [a =
    ANum n]) is very trivial -- even more trivial than the cases that
    we said simply followed from the IH -- yet we have chosen to write
    it out in full. It would be better and clearer to drop it and just
    say, at the top, "Most cases are either immediate or direct from
    the IH. The only interesting case is the one for [APlus]..." We
    can make the same improvement in our formal proof too. Here's how
    it looks: *)

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  elim;
    (* Most cases follow directly by the IH
       or are immediate by definition *)
    try by do [move=> /= a -> a1 -> | ].
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    case; try by move=> /= a1 a2 -> a3 ->.
    + (* a1 = ANum n *) by case => [| ?]; move=> /= _ a ->.
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

(* ================================================================= *)
(** ** Defining New Tactic Notations *)

(** Coq also provides several ways of "programming" tactic scripts.

    - The [Tactic Notation] idiom illustrated below gives a handy way to
      define "shorthand tactics" that bundle several tactics into a
      single command.

    - For more sophisticated programming, Coq offers a small built-in
      programming language called [Ltac] with primitives that can
      examine and modify the proof state.  The details are a bit too
      complicated to get into here (and it is generally agreed that
      [Ltac] is not the most beautiful part of Coq's design!), but they
      can be found in the reference manual and other books on Coq, and
      there are many examples of [Ltac] definitions in the Coq standard
      library that you can use as examples.

    - There is also an OCaml API, which can be used to build tactics
      that access Coq's internal structures at a lower level, but this
      is seldom worth the trouble for ordinary Coq users.

    The [Tactic Notation] mechanism is the easiest to come to grips with,
    and it offers plenty of power for many purposes.  Here's an example. *)

Tactic Notation "simpl_and_try" tactic(c) :=
  move=> /=;
  try c.

(** This defines a new tactical called [simpl_and_try] that takes one tactic [c]
    as an argument and is defined to be equivalent to the tactic [move=> /=; try
    c]. For example, writing "[simpl_and_try reflexivity.]" in a proof would be
    the same as writing "[move=> /=; try reflexivity.]" *)

(* ================================================================= *)
(** ** The [done] Tactic, aka [by []] *)

Ltac my_done :=
  trivial; hnf; intros; solve
   [ do ![solve [trivial | apply: sym_equal; trivial]
         | discriminate | contradiction | split]
   | case not_locked_false_eq_true; assumption
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].

(** There are some unknown tactics and lemmas involved:

    - [trivial]: similar to [reflexivity]

    - [hnf]: normalizes the goal to so-called "head normal form"

    - [solve]: apply the first tactic in the list that solves the goal
      (generates no subgoal)

    - [sym_equal]: lemma corresponding to the symmetry tactic

    - [contradiction]: Try to find a hypothesis [H] in the current
      context that is logically equivalent to [False]. If one is found,
      solve the goal.

    - [not_locked_false_eq_true]: specific to [ssreflect]'s term
      tagging mechanisms: [locked t] is a term that is provably equal
      to [t], but not convertible to [t]

    - [assumption]: Try to find a hypothesis [H] in the context that
      exactly matches the goal; if one is found, behave a bit like
      [apply H]... or rather [exact H], which we didn't spend much
      time on (used by the [done] tactic). *)

(* ================================================================= *)
(** ** The [omega] Tactic *)

(** The [omega] tactic implements a decision procedure for a subset of
    first-order arithmetic (i.e., arithmetic formalized in first-order logic) called _Presburger arithmetic_.  It is based on
    the Omega algorithm invented in 1992 by William Pugh. *)

(**
    If the goal is a universally quantified formula made out of

      - numeric constants, addition ([+] and [S]), subtraction ([-]
        and [pred]), and multiplication by constants (this is what
        makes it Presburger arithmetic),

      - equality ([=] and [<>]) and inequality ([<=]), and

      - the logical connectives [/\], [\/], [~], and [->],

    then invoking [omega] will either solve the goal or tell you that
    it is actually false. *)

Require Import Coq.omega.Omega.

Example silly_presburger_example : forall m n o p, 
   m + n <= n + o /\ o + 3 = p + 3 -> 
   m <= p. 
Proof. 
   by move=> *; omega. 
 Qed. 

(** There are alternatives, like [lia], the linear integer arithmetic sover. 
  - It can do some goals involving nontrivial multiplication 
  - It was supposed to be generally faster
  - Part of a larger family of arithmetic solvers, including [nia] (for non-linear arithmetic), [lra] (for real and rational arithmetic)  *)

(** On the other hand, there are still performance issues
  - As of now, the speed-up claim does not always hold, sometimes to the contrary  
  - Moreover, the present implementation of [lia] may stil fail where [omega] succeeds
  - Some  (Pierre Letouzey) argued that [omega] should be replaced not by [lia], but by [zify;romega]. However, [romega] is deprecated since 8.9 in favour of [lia]
  - We're ecumenic here, experiment with whatever works
  - Not sure if both these libraries are supposed to be loaded at the same time, but we can try 
*)

Require Import Coq.micromega.Lia.  

Example silly_presburger_example2 : forall m n o p, 
   m + n <= n + o /\ o + 3 = p + 3 -> 
   m <= p. 
Proof. 
   by move=> *; lia. 
 Qed. 

(** "_For it is unworthy of excellent men to lose hours like
    slaves in the labor of calculation which could be relegated to
    anyone else if machines were used_." --Gottfried Wilhelm Leibniz, 1685 *)

(** I recommend my excellent
    students to use either the [lia] tactic or the [omega] tactic instead of looking for trivial arithmetical lemmas. *)

(** A historical curiosity, from webpage Cyber Heroes of the past: *) 

(**
"_The Leibniz calculator, which he called the Stepped Reckoner, was based on a new mechanical feature, the stepped drum or Leibniz Wheel. It was a cylinder with nine bar-shaped teeth of different lengths, which increased in equal steps around the drum. This brilliant concept has been used in many later calculators, for example the famous barrel-shaped Curta calculator. When the first wooden prototype of the Stepped Reckoner was constructed Leibniz was able to show it to the Royal Society in London. Although the model did not work properly, the Society members were impressed and asked him to create a proper working model. The final version was only completed in 1674_." *)

(**
"_Although it is believed only two Stepped Reckoners have been constructed, the machine itself was actually lost for more than 200 years. Apparently it was stored in an attic of one of the buildings of the University of Goettingen where a crew of workmen who came to fix a leaking roof accidentally found it in 1879. This model resides in the Hannover State Library. The other model is in the Deutches Museum in Muenchen. In the 20th century a number of replicas of the Leibniz calculator have been built, one of them by IBM. Although quite a few stamps have been issued to commemorate this great scientist, only one philatelic item, a Romanian Postal Card issued in 2004, pictures the Stepped Reckoner_." *)


(* ================================================================= *)
(** ** A Few More Handy Tactics *)

(** Finally, here are some miscellaneous tactics that you may find
    convenient.

     - [move: {H}]: Delete hypothesis [H] from the context. In plain [Ltac] called [clear].

     - [subst x]: Find an assumption [x = e] or [e = x] in the
       context, replace [x] with [e] throughout the context and
       current goal, and clear the assumption. 

     - [subst]: Substitute away _all_ assumptions of the form [x = e]
       or [e = x]. (Note we often use [=> ->] in this way)

     - [constructor]: Try to find a constructor [c] (from some
       [Inductive] definition in the current environment) that can be
       applied to solve the current goal. If one is found, behave like
       [apply c].

     - [try solve]: Tries to solve goal altogether, otherwise leaves
       it unchanged. We'll see it below.
 
     - [have]: a good and compact alternative to [assert], we already
       discussed it. *)

(** We'll see many examples of these in the proofs below. *)

(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** We have presented [aeval] and [beval] as functions defined by
    [Fixpoint]s.  Another way to think about evaluation -- one that we
    will see is often more flexible -- is as a _relation_ between
    expressions and their values.  This leads naturally to [Inductive]
    definitions like the following one for arithmetic expressions... *)

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum  : forall (n: nat),
      aevalR (ANum n) n
  | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

(** As is often the case with relations, we'll find it
    convenient to define infix notation for [aevalR].  We'll write [e
    \\ n] to mean that arithmetic expression [e] evaluates to value
    [n].  (This notation is one place where the limitation to ASCII
    symbols becomes a little bothersome.  The standard notation for
    the evaluation relation is a double down-arrow.  We'll typeset it
    like this in the HTML version of the notes and use a double slash
    as the closest approximation in [.v] files.)  *)

Notation "e '\\' n"
         := (aevalR e n) 
            (at level 50, left associativity)
            : type_scope.

(** Note it's not a great notation. From next lecture on, might replace it with sth else. *)

End aevalR_first_try.

(** In fact, Coq provides a way to use this notation in the definition
    of [aevalR] itself.  This avoids situations where we're working on
    a proof involving statements in the form [e \\ n] but we have to
    refer back to a definition written using the form [aevalR e n].

    We do this by first "reserving" the notation, then giving the
    definition together with a declaration of what the notation
    means. *)

Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.

(* ================================================================= *)
(** ** Inference Rule Notation *)

(** In informal discussions, it is convenient to write the rules for
    [aevalR] and similar relations in the more readable graphical form
    of _inference rules_, where the premises above the line justify
    the conclusion below the line (we have already seen them in the
    Prop chapter). *)

(** For example, the constructor [E_APlus]...

      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)

    ...would be written like this as an inference rule:

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 \\ n1+n2
*)

(** Formally, there is nothing deep about inference rules: they
    are just implications.  You can read the rule name on the right as
    the name of the constructor and read each of the linebreaks
    between the premises above the line and the line itself as [->].
    All the variables mentioned in the rule ([e1], [n1], etc.) are
    implicitly bound by universal quantifiers at the beginning. (Such
    variables are often called _metavariables_ to distinguish them
    from the variables of the language we are defining.  At the
    moment, our arithmetic expressions don't include variables, but
    we'll soon be adding them.)  The whole collection of rules is
    understood as being wrapped in an [Inductive] declaration.  In
    informal prose, this is either elided or else indicated by saying
    something like "Let [aevalR] be the smallest relation closed under
    the following rules...". *)

(** For example, [\\] is the smallest relation closed under these
    rules:

                             -----------                               (E_ANum)
                             ANum n \\ n

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 \\ n1+n2

                               e1 \\ n1
                               e2 \\ n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 \\ n1-n2

                               e1 \\ n1
                               e2 \\ n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 \\ n1*n2
*)

(* ================================================================= *)
(** ** Equivalence of the Definitions *)

(** It is straightforward to prove that the relational and functional
    definitions of evaluation agree, for all arithmetic expressions... *)

Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
 split.
 - (* -> *)
     by elim=> *; subst.
 - (* <- *)
     by elim: a n => /=;
                      do [ (move=> n n0 ->; constructor)
                            | (move=> a IHa1 a0 IHa2 n <-;
                                       first [ apply: E_APlus
                                             | apply: E_AMinus
                                             | apply: E_AMult];
                                     try apply: IHa1;
                                     try apply: IHa2)].
Qed.

(** Or, stated in a more [ssreflect]ish way: *)


Lemma aevalP {a : aexp} {n : nat} : reflect (a \\ n) ((aeval a) =? n).
  Proof.
    apply /equivP; do ?(symmetry; apply aeval_iff_aevalR).
    case eqn: (aeval a =? n); constructor.  
    - by apply Nat.eqb_eq in eqn.
    - by apply Nat.eqb_neq in eqn.      
  Qed.  

(* Sun Jul 14 22:07:54 MSK 2019 *)
