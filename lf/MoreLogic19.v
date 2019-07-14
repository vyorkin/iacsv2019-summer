(** ** More Logic: More about logic, propositions and proofs  *)

(** Adapted from _Software Foundations_  for SemProg@FAU 2013--2019 *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import ssreflect ssrbool ssrfun.

Require Import PeanoNat. (* for basic properties of [nat] functions! *)
Import Nat.

(* ================================================================= *)
(** ** Classical logic and boolean axioms? *)

(** When discussing the behaviour of negation, we have only seen one direction of double negation.
    Note again how we struggle with the doubled notational convention for boolean operations... *)

Theorem real_double_neg_attempt : forall P: Prop, ~ ~P -> P.
Proof.
  rewrite /not.
  move => P hip. (* What now? *)
Abort.

(** Do you remember how negation was handled, say, in the Fitch-style calculus given in GLoIn? *)

(** Similarly ... *)

Theorem ex_middle_attempt : forall P: Prop, ~ ~P \/ P.
Proof.
  rewrite /not.
  move => P. (* What now? Left or right? *)
Abort.

(** The problem is not limited to negation ... *)

Theorem Peirce_law_attempt : forall P Q : Prop, ((P -> Q) ->P) -> P.
Proof.
  move => P Q hip. (** What now? *)
Abort.
  

  
(* ================================================================= *)
(** ** Existential Quantification *)

(**
        - Written [exists x : T, P]. 
        - As with [forall], the type annotation [: T] can be omitted if it can be inferred.
 *)

Print ex.

(* ===>
        Inductive ex (A : Type) (P : A -> Prop) : Prop :=  ex_intro : forall x : A, P x -> exists x, P x
 *)


(** BHK:  a proof of [exists x : S, P(x)] is a pair [<a, b>] where [a] is an element of [S], and [b] is a proof of [P(a)]. *)

(** The core definition is
    for a type former [ex] that can be used to build propositions of
    the form [ex P], where [P] itself is a _function_ from witness
    values in the type [A] to propositions.  The [ex_intro]
    constructor then offers a way of constructing evidence for [ex P],
    given a witness [x] and a proof of [P x].

    The more familiar form [exists x, P x] desugars to an expression
    involving [ex]: *)

Check ex (fun n => n = 2).
(* ===> exists n : nat, n = 2
        : Prop *)

(* ----------------------------------------------------------------- *)
(** *** Existential quantification: proving it. *)

(** The introduction rule for existential quantifier, embodied by the constructor, is

      Gamma |- P (t / x)
    ---------------------------  (exists I)
      Gamma |- exists x, P x
*)

(**
    To prove a statement of the form [exists x, P], we must show that
    [P] holds for some specific choice of value for [x], known as the
    _witness_ of the existential.  This is done in two steps: First,
    we explicitly tell Coq which witness [t] we have in mind by
    invoking the tactic [exists t]; then we prove that [P] holds after
    all occurrences of [x] are replaced by [t].  Here is an example: *)

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  by exists 2.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Existential quantification: using it. *)

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

(** Corresponds to the elimination rule:

        Gamma |- exists x : X, P x    Gamma , P (t / x) |- Q
     -----------------------------------------------------------  (exists E)
                          Gamma  |-  Q
*)

(**
 - The technical restriction is that [t] has to be _fresh_ for both [Gamma] and [Q].
 - But this is precisely what happens when you destruct evidence for an existential statement. 
 - You get a new witness, which is an absolutely arbitrary element of X and your proof must go through regardless of its nature.
 - For example, if X = [Nat], your proof must go through regardless whether x is 0, 42 or 1000.
*)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  move => n [m Hm]; by exists (2 + m).
Qed.


(* ----------------------------------------------------------------- *)
(** ***  Exercises *)

(** **** Exercise: 1 star, standard (dist_not_exists)  

    Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (dist_exists_or)  

    Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)



(* ################################################################# *)
(** * Impredicative Quantification *)

(** [Prop] is a very special type in Coq indeed. *)

(** Universal quantification over [Prop] is not only forming something living in [Prop] again,
    but also (and this is crucial!) this type formed by [forall] is _within its own scope_:
    any piece of evidence for it it can be applied to this very type. *)

(** This is what logicians, philosophers and type theorists know as _impredicative_ quantification. *)

(** Let us see this in an example. *)


(** Let us first recall the alternative definition of negation we suggested in the last lecture *)

Definition our_neg (P : Prop) := forall Q:Prop, P -> Q.

Check our_neg.

(* ===>
     our_neg
     : Prop -> Prop *)

(** Now let us define a piece of evidence (a proof) involving this definition of negation. *)

Definition use_our_neg :=
  fun (P: Prop) (Q: Prop)  (hip : our_neg  P) => hip (our_neg Q).

(** What have we proved, actually? *)

Check use_our_neg.

(* ===>
     use_our_neg
      :  forall P Q : Prop, our_neg P -> P -> our_neg Q *)

(** And, needless to say, the type of [use_our_neg] is again an element of [Prop] *)

Check forall P Q : Prop, our_neg P -> P -> our_neg Q.

(* ===>
        forall P Q : Prop, our_neg P -> P -> our_neg Q
        : Prop *)

(** Of course, this seems just a special case of exfalso anyway. *)

Definition our_exfalso :=
  fun (P: Prop) (Q: Prop)  (hip : our_neg  P) => hip Q.

Check our_exfalso.

(* ===>
     our_exfalso
     : forall P Q : Prop, our_neg P -> P -> Q *)

(** The funny thing is: it would seem that everything we are doing now can be done with arbitary types. *)

Definition our_negT (P : Type) := forall Q:Type, P -> Q.

Check our_negT.

(* ===>
     our_negT
     : Type -> Type *)

(** But it appears that quantification over "arbitrary" types works differently than quantification over propositions. *)

Fail Definition use_our_negT :=
  fun (P: Type) (Q: Type)  (hip : our_negT P) =>  hip (our_negT Q).

(* ===>
        The command has indeed failed with message:
        => Error: The term "our_negT Q" has type "Type@{max(Top.60, Top.61+1)}" while it is expected to have type
 "Type@{Top.61}" (universe inconsistency) (since Coq 8.6; specific indices may differ). *)

(** Universal quantification in the type of [our_negT] does not cover [our_negT] itself:
    [hip] of type [our_negT] cannot be applied to [our_negT]. *)

(** Notice that _ex falso quodlibet_ seems to work with this definition! *)

Definition our_exfalsoT :=
  fun (P: Type) (Q: Type)  (hip : our_negT  P) => hip Q.

Check our_exfalsoT.

(* ===>
     our_exfalsoT
     : forall P Q : Type, our_negT P -> P -> Q *)

(** Coq does a lot of behind-the-screen magic to ensure _predicativity_ of quantification over [Type] (as opposed to [Prop]):
    there is a whole _hierarchy of universes_ invisibe to the naked eye. *)

(** Impredicativity of [Prop] is allowed for several reasons. In particular, because _everything involving [Prop] is ignored during program extraction_! *)

(** Coq is very careful about ensuring that impredicative [Prop] does not "spill out" into other types: 
    this has consequences when defining, e.g., functions which take elements of [Prop] as arguments. *)

(** On the other hand, you also need to be careful when using quantification over "arbitrary" types not to get hit by "universe inconsistency". Those of you who try their hands at the advanced HA on Church numerals may realize this. *)

(** Still, the idea of working with "impredicative" propositional connectives, analogous to working with Church numbers rather than an inductive type, deserves some experimenting. There may well be (possibly advanced) HA on this. *)
 

(* ================================================================= *)
(** ** Programming with Propositions *)

(** The logical connectives that we have seen provide a rich
    vocabulary for _defining complex propositions from simpler ones_. *)

(**
    To illustrate, let's look at how to express the claim that an
    element [x] occurs in a list [l].  Notice that this property has a
    simple recursive structure:

    - If [l] is the empty list, then [x] cannot occur on it, so the
      property "[x] appears in [l]" is simply false.

    - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
      occurs in [l] if either it is equal to [x'] or it occurs in
      [l']. *)

(** We can translate this directly into a straightforward Coq
    function, [In].  In fact, it can  be found in the Coq standard
    library: *)

From Coq Require Import List.
Import List.ListNotations.

Print In.

(* ==> In = 
fun A : Type =>
fix In (a : A) (l : list A) {struct l} : Prop :=
  match l with
  | [] => False
  | b :: m => b = a \/ In a m
  end
     : forall A : Type, A -> list A -> Prop *)

(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested conjunctions. *)

Example In_example_1 : In 4 [3; 4; 5].
Proof.
  move=> /=.
  right. left. 
  by [].
Qed.

(** Another example... *)

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  move => n [H | [H | []]];
    [exists 1 | exists 2]; by rewrite -H. 
Qed.


(** Notice the use of the empty pattern to discharge the last case
    _en passant_. Compare with: *)

Example In_example_2' :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  move => n [H | [H | H]].
  - by exists 1; rewrite -H. 
  - by exists 2; rewrite -H. 
  - case H.
Qed.

(** We can also prove more generic, higher-level lemmas about [In].
    Note, in the next, how [In] starts out applied to a variable and
    only gets expanded when we do case analysis on this variable: *)

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  move => A B f l x.
  elim l => [|x' l' IHl'].
  - (* l = nil, contradiction *)
    cbn.  (* <-- see the expansion of [In] happenning here? I could have finished it with [by cbn], but it was better to see it in "slow motion"... *)
    by move => [].
  - (* l = x' :: l' *)
    cbn.  (* <-- see the expansion of [In] happenning here? *)
    (* WORKED IN CLASS *)
    move => [H | H].
    + by rewrite H; left. 
    + right. apply: IHl' H.
Qed.

(** 
        - This way of defining propositions, though convenient in some cases, also has some drawbacks.  
        - In particular, it is subject to Coq's usual restrictions regarding the definition of recursive functions, e.g., the requirement that they be "obviously terminating."  
        - In the next chapter, we will see how to define propositions _inductively_, a different technique with its own set  of strengths and limitations. *)

(* ================================================================= *)
(** ** Coq vs. Set Theory *)

(** Coq's logical core, the _Calculus of Inductive Constructions_,
    differs in some important ways from other formal systems that are
    used by mathematicians for writing down precise and rigorous
    proofs.  For example, in the most popular foundation for
    mainstream paper-and-pencil mathematics, Zermelo-Fraenkel Set
    Theory (ZFC), a mathematical object can potentially be a member of
    many different sets; a term in Coq's logic, on the other hand, is
    a member of at most one type.  This difference often leads to
    slightly different ways of capturing informal mathematical
    concepts, though these are by and large quite natural and easy to
    work with.  For example, instead of saying that a natural number
    [n] belongs to the set of even numbers, we would say in Coq that
    [ev n] holds, where [ev : nat -> Prop] is a property describing
    even numbers.

    However, there are some cases where translating standard
    mathematical reasoning into Coq can be either cumbersome or
    sometimes even impossible, unless we enrich the core logic with
    additional axioms.  We conclude this chapter with a brief
    discussion of some of the most significant differences between the
    two worlds. *)

(* ================================================================= *)
(** ** Functional Extensionality *)

(**   The equality assertions that we have seen so far mostly have
    concerned elements of inductive types ([nat], [bool], etc.).  But
    since Coq's equality operator is polymorphic, these are not the
    only possibilities. *)

Example function_equality_ex : plus 3 = plus (4 - 1). by []. Qed.

(** In common mathematical practice, two functions [f] and [g] are
    considered equal if they produce the same outputs:

    (forall x, f x = g x) -> f = g

    This is known as the principle of _functional extensionality_. *)

(**
    - _Intensional_ definitions state necessary and sufficient conditions; a
      property, a formula like a defining equation
    - An _extensional_ definition simply enumerates all the elements that fall
      under its scope *)

(** In mathematics, the difference doesn't matter all that much for finite objects. But in the infinite case, it's a completely different world. *)

(** For mathematical functions, an extensional definition is a set-theoretical
    one: identify the function with its graph, i.e., the collection of all the
    pairs related by it. *)

(** From an intensional point of view, what does it mean for two functions
    defined by different equations to be the same? *)

(** Functional extensionality is not one of Coq's basic axioms: the only way to
    show that two functions are equal is by simplification (as we did in the
    proof of [function_equality_ex]). This means that some "reasonable"
    propositions are not provable. *)

Lemma plus_comm_ext : plus = fun n m => m + n.
Proof.
   (* Stuck *)
Abort.


(**    But we can add it to Coq's core logic using the [Axiom]
    command. *)

Module MyFunExt.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
    (forall (x:X), f x = g x) -> f = g.

(** Using [Axiom] has the same effect as stating a theorem and
    skipping its proof using [Admitted], but it alerts the reader that
    this isn't just something we're going to come back and fill in
    later! *)



(**  We can now invoke functional extensionality in proofs: *)

Lemma plus_comm_ext : plus = fun n m => m + n.
Proof.
  apply: functional_extensionality. move => n.
  apply: functional_extensionality. move => m.
  apply: add_comm.
Qed.  

End MyFunExt.
  
(** In fact, there is also a library where the corresponding axiom is hidden: [Coq.Logic.FunctionalExtensionality]  *)

Require Import Logic.FunctionalExtensionality.
Print functional_extensionality.

(** Naturally, we must be careful when adding new axioms into Coq's
    logic, as they may render it inconsistent -- that is, it may
    become possible to prove every proposition, including [False]!
    Unfortunately, there is no simple way of telling whether an axiom
    is safe: hard work is generally required to establish the
    consistency of any particular combination of axioms.  Fortunately,
    it is known that adding functional extensionality, in particular,
    _is_ consistent. *)

(**
    Note that it is possible to check whether a particular proof
    relies on any additional axioms, using the [Print Assumptions]
    command. For instance, if we run it on [plus_comm_ext] proved above, we see
    that it uses the variant of functional extensionality from the module---and, notably, no other axioms. *)

Print Assumptions MyFunExt.plus_comm_ext.
(* ===>
     Axioms:
     MyFunExtfunctional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)




(* Sun Jul 14 22:07:54 MSK 2019 *)
