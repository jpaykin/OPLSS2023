(** * Maps: Total and Partial Maps *)


(* ################################################################# *)
(** * The Coq Standard Library *)

From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
Set Default Goal Selector "!". 
(* If exactly one goal is in focus, apply
    ltac_expr to it. Otherwise the tactic fails.*)

(** If you want to find out how or where a notation is defined, the
    [Locate] command is useful.  For example, where is the natural
    addition operation defined in the standard library? *)

Locate "+".

(** (There are several uses of the [+] notation, but only one for
    naturals.) *)

Print Init.Nat.add.


(* ################################################################# *)
(** * Total Maps *)

Definition total_map (A : Type) := string -> A.

(** Intuitively, a total map over an element type [A] is just a
    function that can be used to look up [string]s, yielding [A]s. *)

(** To compare strings, we use the function [eqb] from the [String]
    module in the standard library. *)
Check String.eqb.

Check String.eqb_refl :
  forall x : string, (x =? x)%string = true.
Check String.eqb_eq :
  forall n m : string, (n =? m)%string = true <-> n = m.
Check String.eqb_neq :
  forall n m : string, (n =? m)%string = false <-> n <> m.

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
  t_update (t_update (t_empty false) 
                     "foo" true)
           "bar" true.







           
(** Next, let's introduce some notations to facilitate working with
    maps. *)

(** First, we use the following notation to represent an empty total
    map with a default value. *)
Notation "'_' '!->' v" := (t_empty v)
  (at level 100 (*order of operations, lower levels bind tighter*),
   right associativity).

Example example_empty := (_ !-> false).

(** We next introduce a convenient notation for extending an existing
    map with a new binding. *)
Notation "x '!->' v ';' m" := (t_update m x v)
          (at level 100,
           v at next level, (* must use parens if v has notation >=100 *)
           right associativity).

(** The [examplemap] above can now be defined as follows: *)

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).

Example update_example1 : examplemap' "baz" = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap' "foo" = true.
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
  
  (* ===>
       Axioms:
       functional_extensionality :
           forall (X Y : Type) (f g : X -> Y),
                  (forall x : X, f x = g x) -> f = g
  
      (We also see [t_update_neq] and [t_update_eq]
       since we haven't yet proven them.) *)
  
  (* QUIZ
  
      Is this provable by just [reflexivity], without
      [functional_extensionality]?
  
        [(fun x => x) = (fun x => 0 + x]
  
      (1) Yes
  
      (2) No
  
   *)






  Example quiz : (fun x => x) = (fun x => 0 + x).
  Proof. reflexivity. Qed.








(* ================================================================= *)
(** ** Map facts *)

(** When we use maps in the next chapter, we'll need several fundamental
    facts about how they behave. *)

(**  First, the empty map returns its default element for all keys: *)

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
      (_ !-> v) x = v.
(* Exercise *) Admitted.

(** Next, if we update a map [m] at a key [x] with a new value [v]
  and then look up [x] in the map resulting from the [update], we
  get back [v]: *)

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
      (x !-> v ; m) x = v.
(* Exercise *) Admitted.

(** On the other hand, if we update a map [m] at a key [x1] and then
  look up a _different_ key [x2] in the resulting map, we get the
  same result that [m] would have given: *)

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
      x1 <> x2 ->
      (x1 !-> v ; m) x2 = m x2.
(* Exercise *) Admitted.
