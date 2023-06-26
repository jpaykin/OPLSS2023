(** * Imp: Simple Imperative Programs *)

(** In this chapter, we take a more serious look at how to use Coq as
    a tool to study other things.  Our case study is a _simple
    imperative programming language_ called Imp, embodying a tiny core
    fragment of conventional mainstream languages such as C and Java.

    Here is a familiar mathematical function written in Imp.

       Z := X;
       Y := 1;
       while Z <> 0 do
         Y := Y * Z;
         Z := Z - 1
       end
*)

(** We concentrate here on defining the _syntax_ and _semantics_ of
    Imp; next time we will develop a theory of _program
    equivalence_ and introduce _Hoare Logic_, a popular logic for
    reasoning about imperative programs. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From OPLSS Require Import Maps.
Set Default Goal Selector "!".

(* ################################################################# *)
(** * Arithmetic and Boolean Expressions *)

(** We'll present Imp in three parts: first a core language of
    _arithmetic and boolean expressions_, then an extension of these
    with _variables_, and finally a language of _commands_ including
    assignment, conditionals, sequencing, and loops. *)

(* ================================================================= *)
(** ** Syntax *)

Module AExp.

(** _Abstract syntax trees_ for arithmetic and boolean expressions: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Evaluation *)

(** _Evaluating_ an arithmetic expression produces a number. *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(** Similarly, evaluating a boolean expression yields a boolean. *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BNeq a1 a2  => negb ((aeval a1) =? (aeval a2))
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BGt a1 a2   => negb ((aeval a1) <=? (aeval a2))
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* QUIZ

    What does the following expression evaluate to?

  aeval (APlus (ANum 3) (AMinus (ANum 4) (ANum 1)))

  (1) true

  (2) false

  (3) 0

  (4) 3

  (5) 6

*)

(* ================================================================= *)
(** ** Optimization *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus  e1 e2 => APlus  (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult  e1 e2 => AMult  (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.

(* ################################################################# *)
(** * Coq Automation *)

(** That last proof was getting a little repetitive.  Time to
    learn a few more Coq tricks... *)

(* ================================================================= *)
(** ** Tacticals *)

(** _Tacticals_ is Coq's term for tactics that take other tactics as
    arguments -- "higher-order tactics," if you will.  *)

(* ----------------------------------------------------------------- *)
(** *** The [try] Tactical *)

(** If [T] is a tactic, then [try T] is a tactic that is just like [T]
    except that, if [T] fails, [try T] _successfully_ does nothing at
    all (rather than failing). *)

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof.
    try reflexivity. (* This just does [reflexivity]. *)
Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* Plain [reflexivity] would have failed. *)
  apply HP. (* We can still finish the proof in some other way. *)
Qed.

(* ----------------------------------------------------------------- *)
(** *** The [;] Tactical (Simple Form) *)

(** In its most common form, the [;] tactical takes two tactics as
    arguments.  The compound tactic [T;T'] first performs [T] and then
    performs [T'] on _each subgoal_ generated by [T]. *)

(** For example: *)

Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.

(** We can simplify this proof using the [;] tactical: *)

Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  (* [destruct] the current goal *)
  destruct n;
  (* then [simpl] each resulting subgoal *)
  simpl;
  (* and do [reflexivity] on each resulting subgoal *)
  reflexivity.
Qed.

(** Using [try] and [;] together, we can get rid of the repetition in
    the proof that was bothering us a little while ago. *)

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* ... but the remaining cases -- ANum and APlus --
       are different: *)
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1 eqn:Ea1;
      (* Again, most cases follow directly by the IH: *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* The interesting case, on which the [try...]
       does nothing, is when [e1 = ANum n]. In this
       case, we have to destruct [n] (to see whether
       the optimization applies) and rewrite with the
       induction hypothesis. *)
    + (* a1 = ANum n *) destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity.   Qed.

(* ----------------------------------------------------------------- *)
(** *** The [repeat] Tactical *)

(** The [repeat] tactical takes another tactic and keeps applying this
    tactic until it fails or until it succeeds but doesn't make any
    progress.

    Here is an example proving that [10] is in a long list using
    [repeat]. *)

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

(** [repeat] can loop forever. *)

Theorem repeat_loop : forall (m n : nat),
  m + n = n + m.
Proof.
  intros m n.
  (* Uncomment the next line to see the infinite loop occur.  You will
     then need to interrupt Coq to make it listen to you again.  (In
     Proof General, [C-c C-c] does this.) *)
  (* repeat rewrite Nat.add_comm. *)
Admitted.

(* ================================================================= *)
(** ** Defining New Tactics *)

(** Coq also provides ways of "programming" tactic scripts:
     - [Ltac]: scripting language for tactics (good for more
       sophisticated proof engineering)
     - [Tactic Notation] for defining tactics with custom concrete
       syntax
     - OCaml tactic scripting API (for wizards)

    [Ltac] is all we need for present purposes.

    For example: *)

Ltac invert H := inversion H; subst; clear H.

(* ================================================================= *)
(** ** The [lia] Tactic *)

(** The [lia] tactic implements a decision procedure for integer linear
    arithmetic, a subset of propositional logic and arithmetic.

    If the goal is a universally quantified formula made out of

      - numeric constants, addition ([+] and [S]), subtraction ([-]
        and [pred]), and multiplication by constants (this is what
        makes it Presburger arithmetic),

      - equality ([=] and [<>]) and ordering ([<=] and [>]), and

      - the logical connectives [/\], [\/], [~], and [->],

    then invoking [lia] will either solve the goal or fail, meaning
    that the goal is actually false.  (If the goal is _not_ of this
    form, [lia] will fail.) *)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. lia.
Qed.

Example add_comm__lia : forall m n,
    m + n = n + m.
Proof.
  intros. lia.
Qed.

Example add_assoc__lia : forall m n p,
    m + (n + p) = m + n + p.
Proof.
  intros. lia.
Qed.

(* ================================================================= *)
(** ** A Few More Handy Tactics *)

(** Finally, here are some miscellaneous tactics that you may find
    convenient.

     - [clear H]: Delete hypothesis [H] from the context.

     - [subst x]: Given a variable [x], find an assumption [x = e] or
       [e = x] in the context, replace [x] with [e] throughout the
       context and current goal, and clear the assumption.

     - [subst]: Substitute away _all_ assumptions of the form [x = e]
       or [e = x] (where [x] is a variable).

     - [rename... into...]: Change the name of a hypothesis in the
       proof context.  For example, if the context includes a variable
       named [x], then [rename x into y] will change all occurrences
       of [x] to [y].

     - [assumption]: Try to find a hypothesis [H] in the context that
       exactly matches the goal; if one is found, solve the goal.

     - [contradiction]: Try to find a hypothesis [H] in the context
       that is logically equivalent to [False].  If one is found,
       solve the goal.

     - [constructor]: Try to find a constructor [c] (from some
       [Inductive] definition in the current environment) that can be
       applied to solve the current goal.  If one is found, behave
       like [apply c].

    We'll see examples of all of these as we go along. *)

(* ################################################################# *)
(** * Evaluation as a Relation *)

(** We have presented [aeval] and [beval] as functions defined by
    [Fixpoint]s.  Another way to think about evaluation -- one that we
    will see is often more flexible -- is as a _relation_ between
    expressions and their values.  This leads naturally to [Inductive]
    definitions like the following... *)

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

(** A standard notation for "evaluates to": *)

Notation "e '==>' n"
         := (aevalR e n)
            (at level 90, left associativity)
         : type_scope.

End aevalR_first_try.

(** With infix notation: *)

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (APlus e1 e2)  ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMult e1 e2)  ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.

(* ================================================================= *)
(** ** Inference Rule Notation *)

(** For example, the constructor [E_APlus]...

      | E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)

    ...would be written like this as an inference rule:

                               e1 ==> n1
                               e2 ==> n2
                         --------------------                (E_APlus)
                         APlus e1 e2 ==> n1+n2
*)

(** There is nothing very deep going on here:
      - a group of inference rules corresponds to a single [Inductive]
        definition
      - each rule's name corresponds to a constructor name
      - above the line are premises
      - below the line is conclusion
      - _metavariables_ like [e1] and [n1] are implicitly universally
        quantified
*)

(** For example, [==>] is the smallest relation closed under these
    rules:

                             -----------                               (E_ANum)
                             ANum n ==> n

                               e1 ==> n1
                               e2 ==> n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 ==> n1+n2

                               e1 ==> n1
                               e2 ==> n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 ==> n1-n2

                               e1 ==> n1
                               e2 ==> n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 ==> n1*n2
*)

(* ================================================================= *)
(** ** Equivalence of the Definitions *)

(** It is straightforward to prove that the relational and functional
    definitions of evaluation agree: *)

Theorem aeval_iff_aevalR : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
 split.
 - (* -> *)
   intros H.
   induction H; simpl.
   + (* E_ANum *)
     reflexivity.
   + (* E_APlus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMinus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMult *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 - (* <- *)
   generalize dependent n.
   induction a;
      simpl; intros; subst.
   + (* ANum *)
     apply E_ANum.
   + (* APlus *)
     apply E_APlus.
     * apply IHa1. reflexivity.
     * apply IHa2. reflexivity.
   + (* AMinus *)
     apply E_AMinus.
     * apply IHa1. reflexivity.
     * apply IHa2. reflexivity.
   + (* AMult *)
     apply E_AMult.
     * apply IHa1. reflexivity.
     * apply IHa2. reflexivity.
Qed.

(** Again, we can make the proof quite a bit shorter using some
    tactics. *)

Theorem aeval_iff_aevalR' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  (* WORK IN CLASS *) Admitted.

End AExp.

(* ================================================================= *)
(** ** Computational vs. Relational Definitions *)

(** Sometimes relational (rather than functional) definitions
    are the only reasonable option... *)

Module aevalR_division.

(* ----------------------------------------------------------------- *)
(** *** Adding division *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).         (* <--- NEW *)

(** What should [aeval] return for a division by zero?? *)

(* ----------------------------------------------------------------- *)
(** *** Adding division, relationally *)

Reserved Notation "e '==>' n"
                  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :          (* <----- NEW *)
      (a1 ==> n1) -> (a2 ==> n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) ==> n3

where "a '==>' n" := (aevalR a n) : type_scope.

(** Notice that the evaluation relation has become _partial_: There
    are some inputs for which it does not specify an output. *)

End aevalR_division.

Module aevalR_extended.

(* ----------------------------------------------------------------- *)
(** *** Adding Nondeterminism *)

(** A _nondeterministic_ number generator: *)

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aexp : Type :=
  | AAny                           (* <--- NEW *)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** What should [aeval] do with nondeterminism?? *)

(* ----------------------------------------------------------------- *)
(** *** Adding nondeterminism, relationally *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any (n : nat) :
      AAny ==> n                        (* <--- NEW *)
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)

where "a '==>' n" := (aevalR a n) : type_scope.

End aevalR_extended.

(* ----------------------------------------------------------------- *)
(** *** Tradeoffs *)

(** Which is better, functional or relational?

    - Functional: take advantage of computation.
    - Relational: more (easily) expressive.
    - Best of both worlds: define both and prove them equivalent.
*)

(* ################################################################# *)
(** * Expressions With Variables *)

(** Let's return to defining Imp, where the next thing we need to do
    is to enrich our arithmetic and boolean expressions with
    variables. To keep things simple, we'll assume that all variables
    are global and that they only hold numbers. *)

(* ================================================================= *)
(** ** States *)

(** Since we'll want to look variables up to find out their current
    values, we'll use total maps from the [Maps] chapter.

    A _machine state_ (or just _state_) represents the current values
    of all variables at some point in the execution of a program. *)

Definition state := total_map nat.

(* ================================================================= *)
(** ** Syntax  *)

(** We can add variables to the arithmetic expressions we had before
    simply by including one more constructor: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)              (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

(** The definition of [bexp]s is unchanged (except that it now refers
    to the new [aexp]s): *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

(* ================================================================= *)
(** ** Notations *)

(** To make Imp programs easier to read and write, we introduce some
    notations and implicit coercions.  You do not need to understand
    exactly what these declarations do.  Briefly, though:
       - The [Coercion] declaration stipulates that a function (or
         constructor) can be implicitly used by the type system to
         coerce a value of the input type to a value of the output
         type.  For instance, the coercion declaration for [AId]
         allows us to use plain strings when an [aexp] is expected;
         the string will implicitly be wrapped with [AId].
       - [Declare Custom Entry com] tells Coq to create a new
         "custom grammar" for parsing Imp expressions and
         programs. The first notation declaration after this tells Coq
         that anything between [<{] and [}>] should be parsed using
         the Imp grammar. Again, it is not necessary to understand the
         details, but it is important to recognize that we are
         defining _new_ interpretations for some familiar operators
         like [+], [-], [*], [=], [<=], etc., when they occur between
         [<{] and [}>]. *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

(** We can now write [3 + (X * 2)] instead  of [APlus 3 (AMult X 2)],
    and [true && ~(X <= 4)] instead of [BAnd true (BNot (BLe X 4))]. *)

Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.

(* ================================================================= *)
(** ** Evaluation *)

(** Now we need to add an [st] parameter to both evaluation
    functions: *)

Fixpoint aeval (st : state) (* <--- NEW *) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- NEW *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (* <--- NEW *) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <> a2}>  => negb ((aeval st a1) =? (aeval st a2))
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{a1 > a2}>   => negb ((aeval st a1) <=? (aeval st a2))
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.

(** We can use our notation for total maps in the specific case of
    states -- i.e., we write the empty state as [(_ !-> 0)]. *)

Definition empty_st := (_ !-> 0).

(** Also, we can add a notation for a "singleton state" with just one
    variable bound to a value. *)
Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).

(* ################################################################# *)
(** * Commands *)

(** Now we are ready define the syntax and behavior of Imp
    _commands_ (or _statements_). *)

(* ================================================================= *)
(** ** Syntax *)

(** Informally, commands [c] are described by the following BNF
    grammar.

     c := skip | x := a | c ; c | if b then c else c end
         | while b do c end
*)

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

(** As we did for expressions, we can use a few [Notation]
    declarations to make reading and writing Imp programs more
    convenient. *)

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

(** For example, here is the factorial function again, written as a
    formal Coq definition.  When this command terminates, the variable
    [Y] will contain the factorial of the initial value of [X]. *)

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     while Z <> 0 do
       Y := Y * Z;
       Z := Z - 1
     end }>.

Print fact_in_coq.

(* ================================================================= *)
(** ** More Examples *)

(** Assignment: *)

Definition plus2 : com :=
  <{ X := X + 2 }>.

Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.

Definition subtract_slowly_body : com :=
  <{ Z := Z - 1 ;
     X := X - 1 }>.

(* ----------------------------------------------------------------- *)
(** *** Loops *)

Definition subtract_slowly : com :=
  <{ while X <> 0 do
       subtract_slowly_body
     end }>.

Definition subtract_3_from_5_slowly : com :=
  <{ X := 3 ;
     Z := 5 ;
     subtract_slowly }>.

(* ----------------------------------------------------------------- *)
(** *** An infinite loop: *)

Definition loop : com :=
  <{ while true do
       skip
     end }>.

(* ################################################################# *)
(** * Evaluating Commands *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [while] loops don't necessarily terminate makes
    defining an evaluation function tricky... *)

(* ================================================================= *)
(** ** Evaluation as a Function (Failed Attempt) *)

(** Here's an attempt at defining an evaluation function for commands,
    omitting the [while] case. *)

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
    | <{ skip }> =>
        st
    | <{ x := a }> =>
        (x !-> (aeval st a) ; st)
    | <{ c1 ; c2 }> =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | <{ if b then c1 else c2 end}> =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | <{ while b do c end }> =>
        st  (* bogus *)
  end.

(* ----------------------------------------------------------------- *)
(** *** Nontermination leads to Inconsistency

     Consider the following "proof object":

        Fixpoint loop_false (n : nat) : False :=
          loop_false n.

     Accepting such a definition would be catastrophic, so Coq
     conservatively rejects _all_ nonterminating programs.
*)

(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** Here's a better way: define [ceval] as a _relation_ rather than a
    _function_ -- i.e., make its result a [Prop] rather than a
    [state], similar to what we did for [aevalR] above. *)

(** We'll use the notation [st =[ c ]=> st'] for the [ceval] relation:
    [st =[ c ]=> st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". *)

(* ----------------------------------------------------------------- *)
(** *** Operational Semantics *)

(** Here is an informal definition of evaluation, presented as inference
    rules for readability:

                           -----------------                            (E_Skip)
                           st =[ skip ]=> st

                           aeval st a = n
                   -------------------------------                      (E_Asgn)
                   st =[ x := a ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ---------------------                           (E_Seq)
                         st =[ c1;c2 ]=> st''

                          beval st b = true
                           st =[ c1 ]=> st'
                --------------------------------------               (E_IfTrue)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                           st =[ c2 ]=> st'
                --------------------------------------              (E_IfFalse)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                    -----------------------------                 (E_WhileFalse)
                    st =[ while b do c end ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ while b do c end ]=> st''
                  --------------------------------                 (E_WhileTrue)
                  st  =[ while b do c end ]=> st''
*)

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)

Example ceval_example1:
  empty_st =[
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (X !-> 2).
  - (* assignment command *)
    apply E_Asgn. reflexivity.
  - (* if command *)
    apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn. reflexivity.
Qed.

(* QUIZ

    Is the following proposition provable?

      forall (c : com) (st st' : state),
        st =[ skip ; c ]=> st' ->
        st =[ c ]=> st'

    (1) Yes

    (2) No

    (3) Not sure

*)
(* QUIZ

    Is the following proposition provable?

      forall (c1 c2 : com) (st st' : state),
          st =[ c1 ; c2 ]=> st' ->
          st =[ c1 ]=> st ->
          st =[ c2 ]=> st'

    (1) Yes

    (2) No

    (3) Not sure

*)
(* QUIZ

    Is the following proposition provable?

      forall (b : bexp) (c : com) (st st' : state),
          st =[ if b then c else c end ]=> st' ->
          st =[ c ]=> st'

    (1) Yes

    (2) No

    (3) Not sure

*)
(* QUIZ

    Is the following proposition provable?

      forall b : bexp,
         (forall st, beval st b = true) ->
         forall (c : com) (st : state),
           ~(exists st', st =[ while b do c end ]=> st')

    (1) Yes

    (2) No

    (3) Not sure

*)
(* QUIZ

    Is the following proposition provable?

      forall (b : bexp) (c : com) (st : state),
         ~(exists st', st =[ while b do c end ]=> st') ->
         forall st'', beval st'' b = true

    (1) Yes

    (2) No

    (3) Not sure

*)

(* ================================================================= *)
(** ** Determinism of Evaluation *)

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Asgn *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard (stack_compiler)

    Old HP Calculators, programming languages like Forth and Postscript,
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a _stack_. For instance, the expression

      (2*3)+(3*(4-2))

   would be written as

      2 3 * 3 4 2 - * +

   and evaluated like this (where we show the program being evaluated
   on the right and the contents of the stack on the left):

      [ ]           |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |

  The goal of this exercise is to write a small compiler that
  translates [aexp]s into stack machine instructions.

  The instruction set for our stack language will consist of the
  following instructions:
     - [SPush n]: Push the number [n] on the stack.
     - [SLoad x]: Load the identifier [x] from the store and push it
                  on the stack
     - [SPlus]:   Pop the two top numbers from the stack, add them, and
                  push the result onto the stack.
     - [SMinus]:  Similar, but subtract the first number from the second.
     - [SMult]:   Similar, but multiply. *)

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

(** Write a function to evaluate programs in the stack language. It
    should take as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and it should return the
    stack after executing the program.  Test your function on the
    examples below.

    Note that it is unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    fewer than two elements.  In a sense, it is immaterial what we do,
    since a correct compiler will never emit such a malformed program.
    But for sake of later exercises, it would be best to skip the
    offending instruction and continue with the next one.  *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Check s_execute.

Example s_execute1 :
     s_execute empty_st []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
(* FILL IN HERE *) Admitted.

Example s_execute2 :
     s_execute (X !-> 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
(* FILL IN HERE *) Admitted.

(** Next, write a function that compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
  s_compile <{ X - (2 * Y) }>
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (execute_app) *)

(** Execution can be decomposed in the following sense: executing
    stack program [p1 ++ p2] is the same as executing [p1], taking
    the resulting stack, and executing [p2] from that stack. Prove
    that fact. *)

Theorem execute_app : forall st p1 p2 stack,
  s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard (stack_compiler_correct) *)

(** Now we'll prove the correctness of the compiler implemented in the
    previous exercise.  Begin by proving the following lemma. If it
    becomes difficult, consider whether your implementation of
    [s_execute] or [s_compile] could be simplified. *)

Lemma s_compile_correct_aux : forall st e stack,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  (* FILL IN HERE *) Admitted.

(** The main theorem should be a very easy corollary of that lemma. *)

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

