(** * Maps: Total and Partial Maps *)


(* ################################################################# *)
(** * The Coq Standard Library *)

From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
Set Default Goal Selector "!". (* If exactly one goal is in focus, apply
                                  ltac_expr to it. Otherwise the tactic fails.*)

(** Documentation for the standard library can be found at
    https://coq.inria.fr/library/.

    The [Search] command is a good way to look for theorems involving
    objects of specific types. *)

(** If you want to find out how or where a notation is defined, the
    [Locate] command is useful.  For example, where is the natural
    addition operation defined in the standard library? *)

Locate "+".

(** (There are several uses of the [+] notation, but only one for
    naturals.) *)

Print Init.Nat.add.

(* ################################################################# *)
(** * Identifiers *)

(** First, we need a type for the keys that we will use to index into
    our maps. We will use the [string] type from Coq's standard library. *)

(** To compare strings, we use the function [eqb] from the [String]
    module in the standard library. *)

Check String.eqb.
Check String.eqb_refl :
  forall x : string, (x =? x)%string = true.


(** We've seen two different ways of expressing logical claims in Coq:
    with _booleans_ (of type [bool]), and with _propositions_ (of type
    [Prop]).

Here are the key differences between [bool] and [Prop]:

                                       bool     Prop
                                       ====     ====
       decidable?                      yes       no
       useable with match?             yes       no
       equalities rewritable?          no        yes
*)

(** The most essential difference between the two worlds is
_decidability_.  Every Coq expression of type [bool] can be
simplified in a finite number of steps to either [true] or
[false] -- i.e., there is a terminating mechanical procedure for
deciding whether or not it is [true].  This means that, for
example, the type [nat -> bool] is inhabited only by functions
that, given a [nat], always return either [true] or [false]; and
this, in turn, means that there is no function in [nat -> bool]
that checks whether a given number is the code of a terminating
Turing machine.  By contrast, the type [Prop] includes both
decidable and undecidable mathematical propositions; in
particular, the type [nat -> Prop] does contain functions
representing properties like "the nth Turing machine halts."

The second row in the table above follow directly from this
essential difference.  To evaluate a pattern match (or
conditional) on a boolean, we need to know whether the scrutinee
evaluates to [true] or [false]; this only works for [bool], not
[Prop].  The third row highlights another important practical
difference: equality functions like [eqb_nat] that return a
boolean cannot be used directly to justify rewriting, whereas
the propositional [eq] can be. *)

(** We will often use a few basic properties of string equality... *)
Check String.eqb_eq :
  forall n m : string, (n =? m)%string = true <-> n = m.
Check String.eqb_neq :
  forall n m : string, (n =? m)%string = false <-> n <> m.


Lemma string_eqb_dec : forall n m : string, n = m \/ n <> m.
      (* This is the law of excluded middle applied to strings---not necessarily
         true for other types! *)
Proof.
    intros m n.
    set (b := (m =? n)%string).
    destruct b eqn:Hb.
    * (* b = true *)
      left.
      apply String.eqb_eq. exact Hb.
    * (* b = false *)
      right.
      apply String.eqb_neq. exact Hb.
Qed.

(* ################################################################# *)
(** * Total Maps *)

(** Our main job in this chapter will be to build a definition of
    partial maps, plus accompanying lemmas about its behavior.

    We will be using _functions_, as opposed to, say,
    lists of key-value pairs, to build maps.  The advantage of
    this representation is that it offers a more "extensional" view of
    maps: two maps that respond to queries in the same way will be
    represented as exactly the same function, rather than just as
    "equivalent" list structures.  This, in turn, simplifies proofs
    that use maps. *)


Definition total_map (A : Type) := string -> A.

(** Intuitively, a total map over an element type [A] is just a
    function that can be used to look up [string]s, yielding [A]s. *)

(** The function [t_empty] yields an empty total map, given a default
    element; this map always returns the default element when applied
    to any string. *)

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

(** More interesting is the map-updating function, which (as always)
    takes a map [m], a key [x], and a value [v] and returns a new map
    that takes [x] to [v] and takes every other key to whatever [m]
    does.  The novelty here is that we achieve this effect by wrapping
    a new function around the old one. *)

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

(** This definition is a nice example of higher-order programming:
    [t_update] takes a _function_ [m] and yields a new function
    [fun x' => ...] that behaves like the desired map. *)

(** For example, we can build a map taking [string]s to [bool]s, where
    ["foo"] and ["bar"] are mapped to [true] and every other key is
    mapped to [false], like this: *)

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

(** Next, let's introduce some notations to facilitate working with
    maps. *)

(** First, we use the following notation to represent an empty total
    map with a default value. *)
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

(** We next introduce a convenient notation for extending an existing
    map with a new binding. *)
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

(** The [examplemap] above can now be defined as follows: *)

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).

(** This completes the definition of total maps.  Note that we
    don't need to define a [find] operation on this representation of
    maps because it is just function application! *)

Example update_example1 : examplemap' "baz" = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap' "foo" = true.
Proof. reflexivity. Qed.

Example update_example3 : examplemap' "quux" = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap' "bar" = true.
Proof. reflexivity. Qed.


(* ================================================================= *)
(** ** Functional Extensionality *)

(** How do we reason about whether two maps are the same? 

    Coq's logic is intentionally quite minimal.  This means that there
    are occasionally some cases where translating standard
    mathematical reasoning into Coq can be cumbersome or even
    impossible, unless we enrich the core logic with additional
    axioms. *)

(** For example, we can write an equality proposition stating
    that two total maps are equal to each other, but we cannot
    prove it by reflexivity. *)

    Example function_equality_ex1 :
    ( "bar" !-> false; _ !-> false )
    =
    ( _ !-> false).
  Proof. try reflexivity. Abort.
  
  (** In common mathematical practice, two functions [f] and [g] are
      considered equal if they produce the same output on every input:
  
      (forall x, f x = g x) -> f = g
  
      This is known as the principle of _functional extensionality_. *)
  
  (** However, functional extensionality is not part of Coq's built-in
      logic.  This means that some apparently "obvious" propositions are
      not provable.
      
      However, if we like, we can add functional extensionality to Coq's
      core using the [Axiom] command. *)
  
  Axiom functional_extensionality : forall {X Y: Type}
                                      {f g : X -> Y},
    (forall (x:X), f x = g x) -> f = g.
  
  (** Defining something as an [Axiom] has the same effect as stating a
      theorem and skipping its proof using [Admitted], but it alerts the
      reader that this isn't just something we're going to come back and
      fill in later! *)
  






  (** We can now invoke functional extensionality in proofs: *)
  

  Example function_equality_ex :
    ( "bar" !-> false; _ !-> false )
    =
    ( _ !-> false).
  Proof.
    apply functional_extensionality.
    intros x.
    unfold t_update.
    unfold t_empty.
    set (b := ("bar" =? x)%string).
    destruct b.
    * reflexivity.
    * reflexivity.
  Qed.
  
  (** Naturally, we must be careful when adding new axioms into Coq's
      logic, as this can render it _inconsistent_ -- that is, it may
      become possible to prove every proposition, including [False],
      [2+2=5], etc.!
  
      Unfortunately, there is no simple way of telling whether an axiom
      is safe to add: hard work by highly trained mathematicians is
      often required to establish the consistency of any particular
      combination of axioms.
  
      Fortunately, it is known that adding functional extensionality, in
      particular, _is_ consistent. *)
  
  (** To check whether a particular proof relies on any additional
      axioms, use the [Print Assumptions] command: *)
  Print Assumptions function_equality_ex.
  
  
  (** **** Exercise: 4 stars, standard (tr_rev_correct)
  
      One problem with the definition of the list-reversing function
      [rev] that we have is that it performs a call to [app] on each
      step; running [app] takes time asymptotically linear in the size
      of the list, which means that [rev] is asymptotically quadratic.
      We can improve this with the following definitions: *)
  
  Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
    match l1 with
    | [] => l2
    | x :: l1' => rev_append l1' (x :: l2)
    end.
  
  Definition tr_rev {X} (l : list X) : list X :=
    rev_append l [].
  
  (** This version of [rev] is said to be _tail-recursive_, because the
      recursive call to the function is the last operation that needs to
      be performed (i.e., we don't have to execute [++] after the
      recursive call); a decent compiler will generate very efficient
      code in this case.
  
      Prove that the two definitions are indeed equivalent. *)
  
  Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
  Proof.
  (* FILL IN HERE *) Admitted.
  (** [] *)


(* ================================================================= *)
(** ** Map facts *)

(** When we use maps in later chapters, we'll need several fundamental
    facts about how they behave. *)

(** Even if you don't bother to work the following exercises,
    make sure you thoroughly understand the statements of the
    lemmas! *)

(** (Some of the proofs require the functional extensionality axiom,
    which was discussed in the Logic chapter of Software Foundations.) *)

(** **** Exercise: 1 star, standard, optional (t_apply_empty)

    First, the empty map returns its default element for all keys: *)

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (t_update_eq)

    Next, if we update a map [m] at a key [x] with a new value [v]
    and then look up [x] in the map resulting from the [update], we
    get back [v]: *)

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (t_update_neq)

    On the other hand, if we update a map [m] at a key [x1] and then
    look up a _different_ key [x2] in the resulting map, we get the
    same result that [m] would have given: *)

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (t_update_shadow)

    If we update a map [m] at a key [x] with a value [v1] and then
    update again with the same key [x] and another value [v2], the
    resulting map behaves the same (gives the same result when applied
    to any key) as the simpler map obtained by performing just
    the second [update] on [m]: *)

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* 2023-06-26 21:16 *)
