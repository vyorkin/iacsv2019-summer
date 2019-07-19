(** * Basics: Functional Programming and First Proofs in Coq *)

(** A loose and enriched adaptation of _Software Foundations_ (Benjamin C. Pierce with numerous coauthors) for Tadeusz Litak for SemProg @FAU Erlangen-Nuremberg 2013--2019. Edition 2017 jointly with Christoph Rauch, edition 2013 jointly with Daniel Gorin. *)

(** Other materials used occasionally in preparation:
- documentation of Coq  (obviously) and of [ssreflect]
- books of Adam Chlipala (CPDT and FRAP),
- later for some more advanced topics also Pierce's "Types and Programming Languages"
- and possibly literature on separation logic (discussed if needed).

But the material is going to be self-contained: no materials other than those provided on StudOn will be needed either for HA or for the final exam.  *)

(* REMINDER:

          #####################################################
          ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
          #####################################################

*)

(* ################################################################# *)
(** * Introduction *)



(** The functional programming style is founded on simple, everyday
    mathematical intuition: If a procedure or method has no side
    effects, then (ignoring efficiency) all we need to understand
    about it is how it maps inputs to outputs -- that is, we can think
    of it as just a concrete method for computing a mathematical
    function.  This is one sense of the word "functional" in
    "functional programming."  The direct connection between programs
    and simple mathematical objects supports both formal correctness
    proofs and sound informal reasoning about program behavior.

    The other sense in which functional programming is "functional" is
    that it emphasizes the use of functions (or methods) as
    _first-class_ values -- i.e., values that can be passed as
    arguments to other functions, returned as results, included in
    data structures, etc.  The recognition that functions can be
    treated as data gives rise to a host of useful and powerful
    programming idioms.

    Other common features of functional languages include _algebraic
    data types_ and _pattern matching_, which make it easy to
    construct and manipulate rich data structures, and sophisticated
    _polymorphic type systems_ supporting abstraction and code reuse.
    Coq offers all of these features.

    The first half of this chapter introduces the most essential
    elements of Coq's functional programming language, called
    _Gallina_.  The second half introduces some basic _tactics_ that
    can be used to prove properties of Coq programs. *)

(* ################################################################# *)
(** * Enumerated Types *)

(** One notable aspect of Coq is that its set of built-in
    features is _extremely_ small.  For example, instead of providing
    the usual palette of atomic data types (booleans, integers,
    strings, etc.), Coq offers a powerful mechanism for defining new
    data types from scratch, with all these familiar types as
    instances.

    Naturally, the Coq distribution comes preloaded with an extensive
    standard library providing definitions of booleans, numbers, and
    many common data structures like lists and hash tables.  But there
    is nothing magic or primitive about these library definitions. *)

(* ================================================================= *)
(** ** Days of the Week *)

(** To see how this definition mechanism works, let's start with
    a very simple example.  The following declaration tells Coq that
    we are defining a new set of data values -- a _type_. *)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(** A more verbose way of doing the same thing ...

Inductive day' : Type :=
  | monday : day'
  | tuesday : day'
  | wednesday : day'
  | thursday : day'
  | friday : day'
  | saturday : day'
  | sunday : day'.
*)



(** The type is called [day], and its members are [monday],
    [tuesday], etc.  The second and following lines of the definition
    can be read "[monday] is a [day], [tuesday] is a [day], etc."

    Having defined [day], we can write functions that operate on
    days. *)

(**  "_We use the keyword [Inductive], in place of [data], [datatype], or [type]. This is not just a trivial surface syntax
difference; inductive types in Coq are much more expressive than garden variety algebraic
datatypes, essentially enabling us to encode all of mathematics, though we begin humbly
in this chapter_." --Adam Chlipala *)

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

(** One thing to note is that the argument and return types of
    this function are explicitly declared.  Like most functional
    programming languages, Coq can often figure out these types for
    itself when they are not given explicitly -- i.e., it can do _type
    inference_ -- but we'll generally include them to make reading
    easier. *)

(* ----------------------------------------------------------------- *)
(** *** How to check if a definition does what it should? *)

(** Having defined a function, we should check that it works, at least on
    some examples.  There are actually three different ways to do this
    in Coq:

        - _execute/evaluate_ it inside Coq by, e.g., using [Compute]
        - _prove_ that it does what it is supposed to do (either on concrete examples or an arbitrary -- universally quantified -- input)
        - _extract_, from our [Definition], a program in some conventional programming language (OCaml, Scheme, or Haskell) and run in a normal way. *)


(* ----------------------------------------------------------------- *)
(** *** Simplification/Execution/Evaluation *)

(** We can use the command [Compute] to evaluate a
    compound expression involving [next_weekday]. *)

Compute (next_weekday friday).
(* ==> monday : day *)

Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)

(** This is not the only way to run our functions in the Coq
_vernacular_. Here are some other options. *)

Eval simpl in (next_weekday (next_weekday saturday)).

Eval cbn in (next_weekday (next_weekday saturday)).
Eval lazy in (next_weekday (next_weekday saturday)).
Eval cbv in (next_weekday (next_weekday saturday)).

(**
- Those of you who have seen some FP before probably imagine what the differences between [cbn], [lazy] and [cbv] are.
- If not, no worries: this is something we may return to much later. You don't have to understand it right now.
- And in such trivial examples, differences do not really matter. *)

(** For completeness, some information from Coq's reference manual:
- [Compute] is a shortcut for [Eval vm_compute in].
- The [cbn] tactic is claimed to be a more principled, faster and more predictable replacement for [simpl].
- My private addition: as some Coq developers also seem to like _Move fast and break things_ lifestyle, in some recent releases (8.6, to wit) good old [simpl] was periodically malfunctioning.
 *)

(** What does the word _tactic_ refer to? This is related to the second thing we can do with our functions: _prove_ stuff about them... *)

(* ----------------------------------------------------------------- *)
(** *** The first encounter with theorems and proofs... *)

(** We can record what we _expect_ the result to be. A "unit test" for our function -- i.e., a mathematical
    claim about its behavior: *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(** Such a declaration does two things:
    - makes an assertion: _the second weekday after_ [saturday] _is_ [tuesday]
    - and it gives the assertion a name that can be used to refer to it later.   *)

(** Notice what happened now in the goals window? This is Coq's way of asking us to finish the job. We have to prove the statement we made. *)

(**
 - The keyword [Example] could be also [Theorem], [Lemma], [Proposition], [Fact], [Remark] or [Corollary].
 - The choice is for our convenience, and doesn't matter from Coq's point of view.
 - It would be a bit stupid though to use a more pompous word than [Example] for something so trivial. *)


(** Here's a proof script giving evidence for the claim. Notice what happens in the goals window when you step through it. *)

Proof. simpl. reflexivity.  Qed.

(** The [simpl] we see here is the same [simpl] we saw before passed as a tactic argument to [Eval]. *)

(** Would other ones work too? Yes. *)

Fact test_next_weekday_alt:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. cbn. reflexivity.
Qed.

(** Note that, as said above, we can use a different keyword
([Lemma] here) and we can prove the same statement, but cannot
use the same name for it as before: *)

Fail Fact test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

(* ==> The command has indeed failed with message:
         Error: test_next_weekday already exists. *)

(** [Fail], as you see, is a way to check if something would malfunction in Coq. *)

Remark test_next_weekday_alt1:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. cbv. reflexivity.
Qed.

Proposition test_next_weekday_alt2:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. lazy. reflexivity.
Qed.

(** Actually, [reflexivity] does such simplifications on its own: we only included this step for illustration purposes and can safely skip it. *)

(* Set Printing All. *)

Theorem test_next_weekday_final:
  (next_weekday (next_weekday (next_weekday saturday))) = wednesday.
Proof. reflexivity.
Qed.

(** In fact, even the keyword [Proof] could have been dispensed with, though we advise against such style of coding. *)

Theorem test_next_weekday_final_alt:
  (next_weekday (next_weekday (next_weekday saturday))) = wednesday.
reflexivity.
Qed.

(** [Qed], on the other hand, cannot be omitted. We will see in a second why. *)

(* ----------------------------------------------------------------- *)
(** *** Aborting failed attempts *)

(** What if we tried something that is simply wrong? *)

Remark test_next_weekday_wrong:
  (next_weekday (next_weekday (next_weekday saturday))) = monday.
Proof.

  (** We are trying to prove something false, so let us just see that reflexivity fails. *)

  Fail reflexivity.

  (** If you don't see the reply in the [goals] window, check the one for [response]... *)

Abort.

(** [Abort] is a way to tell Coq: forget about what we were trying to prove, it should have never been attempted. *)

(* ----------------------------------------------------------------- *)
(** *** Tactics *)

(**
- The things found between [Proof] and [Qed] are _tactics_.

- They are neither parts of Coq's core FP language (Gallina),
  nor vernacular commands.

- Rather, they gradually guide Coq through the construction of a
  _proof term_, which lives in Gallina in the same way ordinary
  programs or type inhabitants do.

- Writing [Qed] is a signal for Coq to type check the term. And
  we can ourselves see this proof term whenever we want to (we
  almost never do, especially now it wouldn't be too
  informative). *)

Print  test_next_weekday_final.

(* ==> test_next_weekday_alt = eq_refl
      : next_weekday (next_weekday saturday) = tuesday *)

(** It doesn't matter for now what this [eq_refl] means. But
note it seems to be the sole content of proofs of the same
statement constructed using a different tactic: *)

Print test_next_weekday_alt.

(* ==> test_next_weekday_alt = eq_refl
     : next_weekday (next_weekday saturday) = tuesday *)

(** Of course, you can imagine things will not be easy with more
complicated theorems and proofs. *)

(** Do we also have a proof for the false theorem we tried? *)

Fail Print test_next_weekday_wrong.

(* ==> The command has indeed failed with message:
         Error: test_next_weekday_wrong not a defined object. *)

(** Indeed. The proof of this Remark was [Abort]ed. *)


(* ----------------------------------------------------------------- *)
(** *** Beyond [Ltac]: [ssreflect] *)

(**
- Coq's basic tactic language is called [Ltac].

- There are ways to extend it. As already mentioned, in this
  lecture (unlike the SF book) we will often use [ssreflect],
  originating in the proof of the Four Color theorem (Georges
  Gonthier, Microsoft Research Cambridge, and collaborators).

- Very suitable also for our purposes, even though we will only
- do very modest things. This is how you call it:
*)

Require Import ssreflect ssrbool.

Theorem test_next_weekday_with_ss_reflect:
  (next_weekday (next_weekday saturday)) = tuesday.

(** This is how natural our proofs can look like now: *)

Proof. by []. Qed.

(** The tactic [by] is built from several other tactics and
actually does far more than just [simpl] and [reflexivity]; we
will explain in due course what exactly happens here. **)

(* ----------------------------------------------------------------- *)
(** *** Aside on program extraction *)

(**
-   We mentioned we can ask Coq to _extract_, from our [Definition], a
    program in some other programming language (OCaml, Scheme, or Haskell) with a high-performance
    compiler.

-   This takes us from _proved-correct algorithms_ written in Gallina to
    _efficient machine code_.

-   (Of course, we are trusting the
    correctness of the OCaml/Haskell/Scheme compiler, and of Coq's
    extraction facility itself, but this is still a big step forward
    from the way most software is developed today.)

-   Indeed, this is
    one of the main uses for which Coq was developed.  We may come back
    to this topic in later chapters.
*)

(* ================================================================= *)
(** ** Booleans *)

(** In a similar way, we could define the standard type [bool] of
booleans, with members [true] and [false]. But the standard
library has already done this for us. *)

(** We could redefine them and override these definitions, but
this would cause unnecessary problems later on. *)

Print bool.

(* ==> [Inductive bool : Set :=  true : bool | false : bool] *)
(**  "[Set] _instead of the more general [Type] declares that we are defining a
datatype that should be thought of as a constituent of programs. There are other
options for defining datatypes in the universe of proofs or in an infinite hierarchy of universes,
encompassing both programs and proofs, that is useful in higher-order constructions_." --Adam Chlipala *)

(** For standard library datatypes, see [Coq.Init.Datatypes] in the Coq library documentation. *)

(* ----------------------------------------------------------------- *)
(** *** First encounter with  function types *)

(** The standard library also defines basic functions on
booleans for us. Let us start with negation [negb]. *)

(** Functions like [negb] itself are also data values, just like
    [true] and [false].  Their types are called _function types_, and of course
    they are written with arrows. *)

(** If we just want to check the type of an existing function
(or any data value) rather than its definition, we can use
[Check]: *)

Check negb.
(* ===> negb : bool -> bool *)

(** The type of [negb], written [bool -> bool] and pronounced
    "[bool] arrow [bool]," can be read, "Given an input of type
    [bool], this function produces an output of type [bool]." *)

(* ----------------------------------------------------------------- *)
(** *** The definition of boolean negation *)

(** But, of course, we are interested in the actual definition
of [negb], not just its type, so we need to use [Print]. *)

Print negb.

(* ==> negb = fun b : bool => if b then false else true
     : bool -> bool *)

(**
 - Note [if ... then... else] instead of the more general [match... with...].
 - Can be used with any datatypes with _exactly two constructors_.
 - Note also the lambda abstraction keyword [fun]. *)


(** Actually, let us try to achieve the same effect. In order
not to override the standard library definitions, let's use
Coq's _module system_. *)

(* ================================================================= *)
(** ** Modules *)

(** Coq provides a _module system_, to aid in organizing large
    developments.  In this course we won't need most of its features,
    but one is useful: If we enclose a collection of declarations
    between [Module X] and [End X] markers, then, in the remainder of
    the file after the [End], these definitions are referred to by
    names like [X.foo] instead of just [foo].  We will use this
    feature to introduce the definition of the type [nat] in an inner
    module so that it does not interfere with the one from the
    standard library (which we want to use in the rest because it
    comes with a tiny bit of convenient special notation).  *)

Module BoolPlayground.

Inductive bool : Type :=
  | true
  | false.

Print bool.

(* ==> Inductive bool : Set :=  true : bool | false : bool *)

(** As you see, our own definition was also automatically taken by Coq to be a [Set], not just an arbitary [Type]. *)

Definition negb (b:bool) : bool :=
  match b with
  | true  => false
  | false => true
  end.

Check negb.
Print negb.


(* ----------------------------------------------------------------- *)
(** *** Boolean functions with two arguments *)

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

(** In plain Coq/Gallina/Ltac, we could achieve the same effect
with [if... then... else]. But [ssreflect] messes things up a
little when it comes to non-standard bools. One needs to be
slightly more verbose: *)

Definition orb (b1:bool) (b2:bool) : bool :=
  if b1 is true then true else b2.

Check andb.
Print andb.

(* ----------------------------------------------------------------- *)
(** *** Unit tests of boolean functions. *)

Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.

(** Of course, we don't need [simpl]. *)

Example test_orb2:  (orb false false) = false.
Proof. reflexivity.  Qed.

(** And we could use [ssreflect] too. *)

Example test_orb3:  (orb false true)  = true.
Proof. by []. Qed.

Example test_orb4:  (orb true  true)  = true. by []. Qed.

(* ----------------------------------------------------------------- *)
(** *** Definining new notation *)

(** We can also introduce some familiar syntax for the boolean
    operations we have just defined. The [Infix] command defines a new
    symbolic notation for an existing definition. *)

Infix "&&" := andb.

(** [Infix] is just a shorthand for a special variant of
[Notation]. More about the more general command later, but
here's the first example: *)

Notation "x || y" := (orb x y).

(** It seems that [Notation] is just a more complicated way of
achieving the same. But we can also set associativity, scope,
precedence/binding/priority level etc.*)

Example test_orb5:  false || false || true = true. by []. Qed.

(** _A note on notation_: In [.v] files, we use square brackets
    to delimit fragments of Coq code within comments; this convention,
    also used by the [coqdoc] documentation tool, keeps them visually
    separate from the surrounding text.  In the html version of the
    files, these pieces of text appear in a [different font]. *)

(** The [Admitted] command tells Coq that we want to skip trying
    to prove this theorem and just accept it as a given.  This can be
    useful for developing longer proofs, since we can state subsidiary
    lemmas that we believe will be useful for making some larger
    argument, use [Admitted] to accept them on faith for the moment,
    and continue working on the main argument until we are sure it
    makes sense; then we can go back and fill in the proofs we
    skipped.  Be careful, though: every time you say [Admitted] you
    are leaving a door open for total nonsense to enter Coq's nice,
    rigorous, formally checked world! *)



(** **** Exercise: 1 star, standard (nandb)

    Remove "[Admitted.]" and complete the definition of the following
    function; then make sure that the [Example] assertions below can
    each be verified by Coq.  (Remove "[Admitted.]" and fill in each
    proof, following the model of the [orb] tests above.) The function
    should return [true] if either or both of its inputs are
    [false]. *)



Definition nandb (b1:bool) (b2:bool) : bool :=
  if b1 is false then true else negb b2.

Example test_nandb1:               (nandb true false) = true.
Proof. by []. Qed.
Example test_nandb2:               (nandb false false) = true.
Proof. by []. Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. by []. Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. by []. Qed.
(** [] *)

(** **** Exercise: 1 star, standard (andb3)

    Do the same for the [andb3] function below. This function should
    return [true] when all of its inputs are [true], and [false]
    otherwise. *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
    | false => false
    | true  => b2 && b3
  end.

Example test_andb31:                 (andb3 true true true) = true.
Proof. by []. Qed.
Example test_andb32:                 (andb3 false true true) = false.
Proof. by []. Qed.
Example test_andb33:                 (andb3 true false true) = false.
Proof. by []. Qed.
Example test_andb34:                 (andb3 true true false) = false.
Proof. by []. Qed.
(** [] *)



(* ----------------------------------------------------------------- *)
(** *** Booleans in the standard library *)

(** Let us leave now our playground and see what the standard library has on offer for booleans. *)

End BoolPlayground.

(** Is our old [nandb] still seen on the global level? *)

Fail Check nandb.

(* ==> The command has indeed failed with message:
         The reference nandb was not found in the current environment. *)

(** Nope. But our old definitions from the module are available if recalled with a proper namespace. *)

Check BoolPlayground.nandb.

(* ==> BoolPlayground.nandb
     : BoolPlayground.bool -> BoolPlayground.bool -> BoolPlayground.bool *)

(** You see this definition operates on the playground booleans, not on the standard ones. *)

(** On the other hand, the obvious functions are available and look just the way we defined them before. *)

Print andb.

(* ==> [andb = fun b1 b2 : bool => if b1 then b2 else false
     : bool -> bool -> bool] *)

Print orb.

(* ==> [orb = fun b1 b2 : bool => if b1 then true else b2
     : bool -> bool -> bool] *)

(** In general, if you want to get Coq to check what has been defined for a given datatype, check [SearchAbout], like  [SearchAbout bool].
    In Proof General, also achieved by ^C ^A ^A.

- IMPORTANT: please do not leave [Search About ...] in the proof scripts you are submitting for HA!
- This blows up entire output, as you can easily check.
- In CoqIDE, there is a separate window to play such games. *)




(* ================================================================= *)
(** ** New Types from Old *)

(** The types we have defined so far are examples of "enumerated
    types": their definitions explicitly enumerate a finite set of
    elements, each of which is just a bare constructor.  Here is a
    more interesting type definition, where one of the constructors
    takes an argument: *)

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).


(** We can define functions on colors using pattern matching just as
    we have done for [day] and [bool]. *)

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary q => false
  end.

(** Since the [primary] constructor takes an argument, a pattern
    matching [primary] should include either a variable (as above --
    note that we can choose its name freely) or a constant of
    appropriate type (as below). *)

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

(** The pattern [primary _] here is shorthand for "[primary] applied
    to any [rgb] constructor except [red]." The _wildcard pattern_ [_]
    has the same effect as the dummy pattern variable [p] in the
    definition of [monochrome]. *)

(* ================================================================= *)
(** ** Tuples *)

(** A single constructor with multiple parameters can be used to
    create a tuple type. As an example, consider representing
    the four bits in a nybble (half a byte). We first define a
    datatype [bit] that resembles [bool] (using the constructors
    [B0] and [B1] for the two possible bit values), and then
    define the datatype [nybble], which is essentially a tuple
    of four bits. *)

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0).
(* ==> bits B1 B0 B1 B0 : nybble *)

(** The [bits] constructor acts as a wrapper for its contents.
    Unwrapping can be done by pattern-matching, as in the [all_zero]
    function which tests a nybble to see if all its bits are O. *)

Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) => true
    | _ => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).
(* ===> true : bool *)

(** Types/sets with finitely many elements, like [bool] are of
course important and useful. But for most purposes, we need at
least natural numbers. How can we define these in Coq? *)

(** Of course, this is where the [Inductive] adjective becomes
meaningful. And of course, they are already defined in the
standard library. But let us again try to have a go at it inside
a [Module] playground. *)

Module NatPlayground.

(* ================================================================= *)
(** ** Numbers *)

(** The types we have defined so far are examples of "enumerated
    types": their definitions explicitly enumerate a finite set of
    elements.  A more interesting way of defining a type is to give a
    collection of _inductive rules_ describing its elements.  For
    example, we can define (a unary representation of) the natural
    numbers as follows: *)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(** The clauses of this definition can be read:
      - [O] is a natural number (note that this is the letter "[O],"
        not the numeral "[0]").
      - [S] is a "constructor" that takes a natural number and yields
        another one -- that is, if [n] is a natural number, then [S n]
        is too. *)

(** This works exactly as you'd expect given the information from ThProg about inductive datatypes and initial algebras. *)

(** Let's look at this in a little more detail. *)

(** Every inductively defined set ([day], [nat], [bool], etc.) is
    actually a set of _expressions_ built from _constructors_
    like [O], [S], [true], [false], [monday], etc. The
    definition of [nat] says how expressions in the set [nat] can be
    built:

    - [O] and [S] are constructors; the expression [O] belongs
    - to the set [nat]; if [n] is an expression belonging to the
    - set [nat], then [S n] is also an expression belonging to the
    - set [nat]; and expressions formed in these two ways are the
    - only ones belonging to the set [nat]. *)

(** The same rules apply for our definitions of [day] and
    [bool]. (The annotations we used for their constructors are
    analogous to the one for the [O] constructor, indicating that they
    don't take any arguments.)

    The above conditions are the precise force of the [Inductive]
    declaration.  They imply that the expression [O], the expression
    [S O], the expression [S (S O)], the expression [S (S (S O))], and
    so on all belong to the set [nat], while other expressions built
    from data constructors, like [true], [andb true false], [S (S
    false)], and [O (O (O S))] do not.

    A critical point here is that what we've done so far is just to
    define a _representation_ of numbers: a way of writing them down.
    The names [O] and [S] are arbitrary, and at this point they have
    no special meaning -- they are just two different marks that we
    can use to write down numbers (together with a rule that says any
    [nat] will be written as some string of [S] marks followed by an
    [O]).  If we like, we can write essentially the same definition
    this way: *)

Inductive nat' : Type :=
  | stop : nat'
  | tick : nat' -> nat'.

(** The _interpretation_ of these marks comes from how we use them to
    compute. *)

(** We can do this by writing functions that pattern match on
    representations of natural numbers just as we did above with
    booleans and days -- for example, here is the predecessor
    function: *)

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(** The second branch can be read: "if [n] has the form [S n']
    for some [n'], then return [n']."  *)

End NatPlayground.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

(** Because natural numbers are such a pervasive form of data,
    Coq provides a tiny bit of built-in magic for parsing and printing
    them: ordinary arabic numerals can be used as an alternative to
    the "unary" notation defined by the constructors [S] and [O].  Coq
    prints numbers in arabic form by default: *)

Check (S (S (S (S O)))).
  (* ===> 4 : nat *)
Compute (minustwo 4).
  (* ===> 2 : nat *)

(** The constructor [S] has the type [nat -> nat], just like the
    functions [minustwo] and [pred]: *)

Check S.
Check pred.
Check minustwo.

(** These are all things that can be applied to a number to yield a
    number.  However, there is a fundamental difference between the
    first one and the other two: functions like [pred] and [minustwo]
    come with _computation rules_ -- e.g., the definition of [pred]
    says that [pred 2] can be simplified to [1] -- while the
    definition of [S] has no such behavior attached.  Although it is
    like a function in the sense that it can be applied to an
    argument, it does not _do_ anything at all!  It is just a way of
    writing down numbers.  (Think about standard arabic numerals: the
    numeral [1] is not a computation; it's a piece of data.  When we
    write [111] to mean the number one hundred and eleven, we are
    using [1], three times, to write down a concrete representation of
    a number.)

    For most function definitions over numbers, just pattern matching
    is not enough: we also need recursion.  For example, to check that
    a number [n] is even, we may need to recursively check whether
    [n-2] is even.  To write such functions, we use the keyword
    [Fixpoint]. *)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(** We can define [oddb] by a similar [Fixpoint] declaration, but here
    is a simpler definition: *)

Definition oddb (n:nat) : bool   :=   negb (evenb n).

Example test_oddb1:    oddb 1 = true.
Proof. reflexivity. Qed.

Example test_oddb2:    oddb 4 = false. by []. Qed.

(* ----------------------------------------------------------------- *)
(** *** Multi-argument recursive functions. *)

(** Addition and multiplication provide  examples of multi-argument recursive functions.

It is instructive to develop them on our own. As you can already guess, they will duplicate those in the standard library, so we need to wrap things up in a [Module] again. *)

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(** Adding three to two now gives us five, as we'd expect. *)

Compute (plus 3 2).

(** The simplification that Coq performs to reach this conclusion can
    be visualized as follows: *)

(*  [plus (S (S (S O))) (S (S O))]
==> [S (plus (S (S O)) (S (S O)))]
      by the second clause of the [match]
==> [S (S (plus (S O) (S (S O))))]
      by the second clause of the [match]
==> [S (S (S (plus O (S (S O)))))]
      by the second clause of the [match]
==> [S (S (S (S (S O))))]
      by the first clause of the [match]
*)

(** As a notational convenience, if two or more arguments have
    the same type, they can be written together.  In the following
    definition, [(n m : nat)] means just the same as if we had written
    [(n : nat) (m : nat)]. *)

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
(* Proof. simpl. reflexivity.  Qed. *)
Proof. by []. Qed.

(** You can match two expressions at once by putting a comma
    between them: *)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O   , _    => O
  | S _ , O    => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

(* ----------------------------------------------------------------- *)
(** *** More on notation *)

(** Coq's standard library defines basic aritmetical notation for operations on numbers. *)

Check ((2 + 3) * 2).


Eval simpl in ((2 + 3) * 2).
Eval cbn in ((2 + 3) * 2).
Eval simpl in (mult (plus 2 3) 2).



(* ----------------------------------------------------------------- *)
(** *** Recursive boolean functions for testing equality of natural numbers *)

(** We now define a function [beq_nat], which tests
    [nat]ural numbers for [eq]uality, yielding a [b]oolean.  Note the
    use of nested [match]es; we could also have used a simultaneous
    match, as we did in [minus]. And to simplify the notation, we could have also used [if ... then ... else ...] *)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

(** A shorter way of doing the same thing with SSReflect... *)

Fixpoint beq_nat' (n m : nat) : bool :=
  if n is S n' then
    if m is S m' then beq_nat n' m' else false
  else
    if m is S m' then false else true.

(** With [ssreflect] as in [mathcomp], one used a different
treatment of [nat] ... *)

(** In fact, [ssreflect] relies very much on boolean functions.
We will learn more about this in the weeks to follow, but
already in this lecture this is going to be a constant theme. *)

(** For the time being, as a trivial exercise, remove [Admitted]
and fill in the proof of this unit test. *)

Example beqnatid_unit : beq_nat 1 1 = beq_nat' 1 1.
Proof.
  (* WORKED IN CLASS *)
    by []. Qed.

(** Could we show this in full generality? Yes, but this
requires induction, and we will only start with induction next
week (or next lecture). *)




(** Similarly the [leb] function tests whether its first argument is less than or
  equal to its second argument, yielding a boolean. *)


Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

(** **** Exercise: 1 star, standard (leb')  *)

(** Rewrite this definition in a more compact way, possibly
using [ssreflect] syntax. *)

Fixpoint leb'' (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Fixpoint leb' (n m : nat) : bool :=
  if n is (S n') then
    if m is (S m') then
      leb' n' m'
    else
      false
  else
    true.

Example test_leb1:             (leb 2 4) = true.
Proof. (* WORKED IN CLASS *) by []. Qed. Example test_leb2:             (leb 4 2) = (beq_nat 4 2).
Proof. (* WORKED IN CLASS *) by []. Qed. (** [] *)


(** Since we'll be using these (especially [eqb]) a lot, let's
    give them infix notations. *)

Notation "x =? y" := (beq_nat x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

(** Here you see some additional features of [Notation]. *)

(** Coq uses precedence levels from 0 to 100 (stronger are
    lower), and _left_, _right_, or _no_ associativity. *)

(** Each notation symbol is also associated with a _notation
scope_. Occasionally, it is necessary to help Coq out with
percent-notation by writing [(x*y)%nat], and sometimes in what Coq
prints it will use [%nat] to indicate what scope a notation is in.
*)

(** Pro tip: Coq's notation mechanism is not especially
    powerful. Don't expect too much from it! *)

Example test_leb3':             (4 <=? 2) = false.
Proof. simpl. reflexivity.  Qed.

(** **** Exercise: 1 star, standard (ltb)

    The [ltb] function tests natural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Instead of making up a new [Fixpoint] for
    this one, define it in terms of a previously defined
    function.  (It can be done with just one previously defined
    function, but you can use two if you need to.) *)

Definition ltb (n m : nat) : bool := ((n <=? m) && (negb (n =? m))).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1:             (ltb 2 2) = false.
Proof. by []. Qed.
Example test_ltb2:             (ltb 2 4) = true.
Proof. by []. Qed.
Example test_ltb3:             (ltb 4 2) = false.
Proof. by []. Qed.
(** [] *)

(* Sun Jul 14 22:07:53 MSK 2019 *)
