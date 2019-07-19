(** * ListAndPoly19: Working with Structured Data and Polymorphism *)

(** Adapted from the Software Foundations for SemProg@FAU 2013--2019 *)



Set Warnings "-notation-overridden,-parsing".
From Coq Require Import ssreflect ssrbool.

(* ################################################################# *)
(** * Separate Compilation *)

(** Before getting started, let us try again  to import our
    definitions from one of the previous chapters: *)

From LF19 Require Export Basics19.

(** For the [Require Export] to work, Coq needs to be able to
    find a compiled version of [Basics19.v], called [Basics19.vo], in a directory
    associated with the prefix [LF].  This file is analogous to the [.class]
    files compiled from [.java] source files and the [.o] files compiled from
    [.c] files.

    First you need a file named [_CoqProject] containing the following line:

      [-Q . LF19]

    This maps the current directory "[.]", which contains [Basics19.v] etc.,
    to the prefix (or "logical directory") "[LF19]".
    PG and CoqIDE read [_CoqProject] automatically, so they know to where to
    look for the file [Basics19.vo] corresponding to the library [LF19.Basics19].

    Once [_CoqProject] is thus created, there are various ways to build
    [Basics19.vo]:

     - In Proof General: The compilation can be made to happen automatically
       when you submit the [Require] line above to PG, by setting the emacs
       variable [coq-compile-before-require] to [t].

     - In CoqIDE: Open [Basics19.v]; then, in the "Compile" menu, click
       on "Compile Buffer".

     - From the command line: Generate a [Makefile] using the [coq_makefile]
       utility, that comes installed with Coq (if you obtained the whole
       volume as a single archive, a [Makefile] should already exist
       and you can skip this step):

         [coq_makefile -f _CoqProject *.v -o Makefile]

       Note: You should rerun that command whenever you add or remove Coq files
       to the directory.

       Then you can compile [Basics19.v] by running [make] with the corresponding
       [.vo] file as a target:

         [make Basics19.vo]

       All files in the directory can be compiled by giving no arguments:

         [make]

       Under the hood, [make] uses the Coq compiler, [coqc].  You can also
       run [coqc] directly:

         [coqc -Q . LF19 Basics19.v]

       But [make] also calculates dependencies between source files to compile
       them in the right order, so [make] should generally be prefered over
       explicit [coqc].

    If you have trouble (e.g., if you get complaints about missing
    identifiers later in the file), it may be because the "load path"
    for Coq is not set up correctly.  The [Print LoadPath.] command
    may be helpful in sorting out such issues.

    In particular, if you see a message like

        [Compiled library Foo makes inconsistent assumptions over
        library Bar]

    check whether you have multiple installations of Coq on your machine.
    It may be that commands (like [coqc]) that you execute in a terminal
    window are getting a different version of Coq than commands executed by
    Proof General or CoqIDE.

    - Another common reason is that the library [Bar] was modified and
      recompiled without also recompiling [Foo] which depends on it.  Recompile
      [Foo], or everything if too many files are affected.  (Using the third
      solution above: [make clean; make].)

    One more tip for CoqIDE users: If you see messages like [Error:
    Unable to locate library Basics19], a likely reason is
    inconsistencies between compiling things _within CoqIDE_ vs _using
    [coqc] from the command line_.  This typically happens when there
    are two incompatible versions of [coqc] installed on your
    system (one associated with CoqIDE, and one associated with [coqc]
    from the terminal).  The workaround for this situation is
    compiling using CoqIDE only (i.e. choosing "make" from the menu),
    and avoiding using [coqc] directly at all. *)


(* ################################################################# *)
(** * Lists of Numbers *)

(** Generalizing the definition of pairs, we can describe the
    type of _lists_ of numbers like this: "A list is either the empty
    list or else a pair of a number and another list." *)

Inductive natlist : Type :=
  | nil_nat : natlist
  | con_nat : nat -> natlist -> natlist.

(** Of course, this is something you have seen in functional
programming and all of you expect to see a polymorphic
definition. This is how it looks like in the standard library:
*)

Print list.

(** ===>

Inductive list (A : Type) : Type :=  nil : list A | cons : A -> list A -> list A
*)

(** [list] is a _function_ from types to (inductively
    defined) types. *)

(** Note what Coq tells us:

For nil: Argument A is implicit and maximally inserted
For cons: Argument A is implicit and maximally inserted
*)

Check nil.
(** ===>

nil
     : list ?A
where
?A : [ |- Type]
*)

Check cons.
(** ===>

cons
     : ?A -> list ?A -> list ?A
where
?A : [ |- Type]
*)

(** We can force the implicit arguments to be explicit by
   prefixing the function name with [@]. *)

Check @nil.

(** ===>

@nil
     : forall A : Type, list A
*)

(** Lots of standard notations are already defined for us: *)

Require Export Coq.Lists.List.
Export ListNotations.

Check (1 :: 2 :: nil).

(** ===>

[1; 2]
     : list nat
*)

(** If you want to see how notation is defined, here is how you
do it in [ssreflect]: *)

Locate "_ :: _".

(** ===>

Notation
"x :: y" := cons x y : list_scope (default interpretation)
*)

(** Note the use of [list_scope] *)

(** If you want to see a list of theorems, lemmas etc. using
this notation, replace [Locate] with [Search] above. Warning:
this is going to be a long list! *)

(* ================================================================= *)
(** ** Standard functions on lists *)

(* ----------------------------------------------------------------- *)
(** *** Repeat *)

Print repeat.

(** ===>

repeat =
fun A : Type =>
fix repeat (x : A) (n : nat) {struct n} : list A := match n with
                                                    | 0 => []
                                                    | S k => x :: repeat x k
                                                    end
     : forall A : Type, A -> nat -> list A

Argument A is implicit
Argument scopes are [type_scope _ nat_scope]
*)

(** Clear what it does? *)


(* ----------------------------------------------------------------- *)
(** *** Append *)

Print app.

(** ===>

app =
fun A : Type =>
fix app (l m : list A) {struct l} : list A := match l with
                                              | [] => m
                                              | a :: l1 => a :: app l1 m
                                              end
     : forall A : Type, list A -> list A -> list A
*)

Locate "_ ++ _".

(** ===>

Notation
"x ++ y" := app x y : list_scope (default interpretation)
*)

Compute  [1;2;3] ++ [4;5].


(* ----------------------------------------------------------------- *)
(** *** Head (with default) and Tail *)

Print hd.

(** ===>

hd =
fun (A : Type) (default : A) (l : list A) => match l with
                                             | [] => default
                                             | x :: _ => x
                                             end
     : forall A : Type, A -> list A -> A
*)

(** As you can guess, not a very satisfying solution for the empty list. *)

(** Here is tail, for completness *)

Print tl.

(** ===>

tl =
fun (A : Type) (l : list A) => match l with
                               | [] => []
                               | _ :: m => m
                               end
     : forall A : Type, list A -> list A
*)

(* ----------------------------------------------------------------- *)
(** *** Option types *)

(** An obvious improvement would be to use option types for head. Obviously, Coq defines them for us too. *)

Print option.

(** ====>

Inductive option (A : Type) : Type :=  Some : A -> option A | None : option A
*)

(** Define the obvious [option_hd] function. This is how you
make an argument implicit, by the way. *)

Fixpoint option_hd {A : Type} (l: list A) : option A :=
  match l with
    | nil => None
    | x :: l' => Some x
  end.

Example test_hd1: option_hd [1;2;3] = Some 1.
Proof.  by [].
Example test_hd2 (A:Type) : @option_hd A [] = None.
Proof.  by [].

(* ----------------------------------------------------------------- *)
(** *** First non-trivial proof for lists *)

(** These work just by case analysis. *)

Theorem hd_is_hd1 : forall (A : Type) (l : list A) (default : A),
    option_hd l = None -> hd default l = default.
Proof.
  move => T l1 default H.
  case l1.
  - reflexivity.
  - move => x l2.
    case l2.
    * simpl.
    -

Theorem hd_is_hd2 : forall (A : Type) (l : list A) (default : A) (a: A), option_hd l = Some a -> hd default l = a.
Proof.
(* FILL IN HERE *) Admitted.

(* ----------------------------------------------------------------- *)
(** *** Length  *)

Print length.

(**  ===>

length =
fun A : Type => fix length (l : list A) : nat := match l with
                                                 | [] => 0
                                                 | _ :: l' => S (length l')
                                                 end
     : forall A : Type, list A -> nat
*)

(* ----------------------------------------------------------------- *)
(** *** Reverse *)

Print rev.

(**  ===>

rev =
fun A : Type => fix rev (l : list A) : list A := match l with
                                                 | [] => []
                                                 | x :: l' => rev l' ++ [x]
                                                 end
     : forall A : Type, list A -> list A
*)


(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** Complete the definitions of [oddmembers] and
    [countoddmembers] below. Have a look at the tests to understand
    what these functions should do. *)

Require Import Nat.

(** This gives us a function [odd] ... *)


Fixpoint oddmembers (l:list nat) : (list nat)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
(* FILL IN HERE *) Admitted.

Definition countoddmembers (l:list nat) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  (* FILL IN HERE *) Admitted.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  (* FILL IN HERE *) Admitted.

Example test_countoddmembers3:
  countoddmembers nil = 0.
  (* FILL IN HERE *) Admitted.

(** It seems we could think of a more general pattern here. *)

(** For example, we could define a function removing all zero elements from lists of natural numbers. Or keep only true values on a list of booleans. Or only lists of length one on a list of lists ... *)


(* ================================================================= *)
(** **  Higher-Order Functions *)

(** Functions that manipulate other functions are often called
    _higher-order_ functions. *)


(** Here is an useful higher-order function, taking a list
    of [X]s and a _predicate_ on [X] (a function from [X] to [bool])
    and "filtering" the list, returning a new list containing just
    those elements for which the predicate returns [true]. *)

Print filter.

(** ====>

filter =
fun (A : Type) (f : A -> bool) =>
fix filter (l : list A) : list A :=
  match l with
  | [] => []
  | x :: l0 => if f x then x :: filter l0 else filter l0
  end
     : forall A : Type, (A -> bool) -> list A -> list A
*)

(** For example, if we apply [filter] to the predicate [even]
    (from the standard library) and a list of numbers [l], it returns
    a list containing just the even members of [l]. *)

Example test_filter1: filter odd [1;2;3;4] = [1;3].
Proof. by [].  Qed.

(** We now need our boolean equality on [nat]. *)

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l =? 1).

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; nil; [8] ]
  = [ [3]; [4]; [8] ].
Proof. by [].  Qed.



(* ================================================================= *)
(** ** Map *)

(** Another handy higher-order function is [map]. *)

Print map.

(** ===>

map =
fun (A B : Type) (f : A -> B) =>
fix map (l : list A) : list B := match l with
                                 | [] => []
                                 | a :: t => f a :: map t
                                 end
     : forall A B : Type, (A -> B) -> list A -> list B
*)

(* ----------------------------------------------------------------- *)
(** *** Flat map *)

Print flat_map.

(** ===>

flat_map =
fun (A B : Type) (f : A -> list B) =>
fix flat_map (l : list A) : list B := match l with
                                      | [] => []
                                      | x :: t => f x ++ flat_map t
                                      end
     : forall A B : Type, (A -> list B) -> list A -> list B
*)

Example testflatmap : flat_map (fun n => [n;n+1;n+2]) [1;5;10]
                      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
Proof. by []. Qed.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. by [].  Qed.

(** Note how we use anonymous functions here? *)

(** A mapping function for [option]s: *)

Print option_map.

(** ===>

option_map =
fun (A B : Type) (f : A -> B) (o : option A) => match o with
                                                | Some a => Some (f a)
                                                | None => None
                                                end
     : forall A B : Type, (A -> B) -> option A -> option B
*)

(* ================================================================= *)
(** ** Fold *)

(** An even more powerful higher-order function is called
    [fold].  This function is the inspiration for the "[reduce]"
    operation that lies at the heart of Google's map/reduce
    distributed programming framework. *)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** Intuitively, the behavior of the [fold] operation is to
    insert a given binary operator [f] between every pair of elements
    in a given list.  For example, [ fold plus [1;2;3;4] ] intuitively
    means [1+2+3+4].  To make this precise, we also need a "starting
    element" that serves as the initial second input to [f].  So, for
    example,

   fold plus [1;2;3;4] 0

    yields

   1 + (2 + (3 + (4 + 0))).

    Some more examples:
*)

Check (fold andb).
(* ===> fold andb : list bool -> bool -> bool *)

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. by []. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. by []. Qed.

(** Note we have to be careful with polymorphism in the next example *)

Check @fold (list nat).

Example fold_example3 :
  @fold (list nat) (list nat) (@app nat) [[1];nil;[2;3];[4]] nil = [1;2;3;4].
Proof. by []. Qed.





(** Many common functions on lists can be implemented in terms of
   [fold].  For example, here is an alternative definition of [length]: *)

Definition fold_length (X : Type) (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

(** Note it is quite useful here that the function f in the
definition of [fold] can take arguments of mixed type. *)

Arguments fold_length {X}.

(** This is an alternative way of making arguments implicit, by
the way. Sometimes it might make sense: e.g., you want to make
constructors of a polymorphic type easier to write, but the type
to remain explicitly polymorphic. *)

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. by []. Qed.

(** Prove the correctness of [fold_length]. This is our first
encounter with induction on lists. *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
(* WORKED IN CLASS *)
Proof.
  move => ?.
  elim => [|hl tl IHl] /= //.
    by rewrite -IHl.
Qed.

Theorem fold_length_correct' : forall X (l : list X),
  fold_length l = length l.
(* WORKED IN CLASS *)
Proof.
  move => ?.
  by elim=> /= [|hl tl <-].
Qed.

(** We can do the same thing with [map], i.e., define it using
[fold]. Can you see how? *)

(* ----------------------------------------------------------------- *)
(** *** An example of a more complicated proof *)

(** The strandard library has a lot of useful theorems about
list programs and transformations we have seen. One example: *)

Check rev_length.

(** ====>

rev_length
     : forall (A : Type) (l : list A), length (rev l) = length l
*)

(** How do we prove it? *)

Theorem rev_length_firsttry : forall X (l : list X),
  length (rev l) = length l.
Proof.
  intros X l. induction l as [| n l' IHl'].
  - (** l = [] *)

    reflexivity. (* So far, so good, obviously... *)


  - (** l = n :: l' *)

    (** This is the tricky case.  Let's begin as usual
       by simplifying. *)

    simpl.

    (** Now we seem to be stuck: the goal is an equality
       involving [++], but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)

    rewrite <- IHl'.

    (** ... but now we can't seem to go any further. *)

Abort.

(* ----------------------------------------------------------------- *)
(** *** With a little help from a lemma *)

(** So let's take the equation relating [++] and [length] that
    would have enabled us to make progress and prove it as a separate
    lemma.
*)

Theorem app_len : forall X (l1 l2 : list X),
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  move => ?.
  elim => [| n l1' IHl1'] /= .
  - reflexivity.
  - move => ?. by rewrite IHl1'. Qed.


(** Note that, to make the lemma as general as possible, we
    quantify over _all_ [natlist]s, not just those that result from an
    application of [rev].  This should seem natural, because the truth
    of the goal clearly doesn't depend on the list having been
    reversed.  Moreover, it is easier to prove the more general
    property. *)

(** The same thing is in the standard library as [app_length]. *)

(** Something else we are missing: commutativity of addition. We have proved it though. *)


From LF19 Require Import FirstProofs19.

(** Now we can complete the original proof. *)

Theorem rev_len : forall X (l : list X),
  length (rev l) = length l.
Proof.
  move => ?.
  elim => [| n l' IHl'] /=.
  - (* l = nil *)
    by [].
  - (* l = cons *)
    (* WORKED IN CLASS *)
      by rewrite app_len plus_comm IHl'.
Qed.

(* ================================================================= *)
(** ** More polymorphic types *)

Print prod.

(** ===>

Inductive prod (A B : Type) : Type :=  pair : A -> B -> A * B

For pair: Arguments A, B are implicit and maximally inserted
*)

(** You see the notation for products here. Here are projections: *)

Print fst.
Print snd.

(**

fst = fun (A B : Type) (p : A * B) => let (x, _) := p in x
     : forall A B : Type, A * B -> A
snd = fun (A B : Type) (p : A * B) => let (_, y) := p in y
     : forall A B : Type, A * B -> B
*)

(* ----------------------------------------------------------------- *)
(** *** Zipping and unzipping *)

(** Here are some standard functions that combine products and lists *)

Print combine.
Print split.

(** Are those two functions inverses of each other? *)

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  reflexivity.
Qed.

(* Sun Jul 14 22:07:53 MSK 2019 *)
