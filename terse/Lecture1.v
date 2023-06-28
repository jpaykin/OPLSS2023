(** * Basics: Functional Programming in Coq *)

(** * Lecture 1

Coq consists of a
    dependently-typed
    functional programming langauge (Gallina)
as well as an
    interactive therorem prover.
*)

(* ================================================================= *)
(** ** A functional programming langauge *)


Module Nat.
    (** Unary natural numbers are either
        - 0 (the letter "O")
        - the successor of a natural number [S n]
    *)
    Inductive nat : Set :=
    | O : nat 
    | S (n : nat) : nat.

    (** We can check the types of terms we have defined, 
    or print out
        definitions, using the [Check] and [Print] commands. *)
    Check nat. (* : Set *)
    Check S. (* : nat -> nat *)
    Print nat.








    (** We can define functions over natural numbers by case analysis. *)
    Definition pred (n : nat) : nat :=
        match n with
        | O => O
        | S n' => n'
        end.
    Check pred.











    (** We can define recursive functions using [Fixpoint]. *)
    Fixpoint plus (n1 n2 : nat) : nat :=
        match n1 with
        | O => n2
        | S n1' => S (plus n1' n2)
        end.

    (** Notations can be a bit bulky and hard to define, but they are
        very useful for readability. *)
    Notation "n1 + n2" := (plus n1 n2).

    (** You can evaluate tests using [Compute]. *)
    Compute (S (S O) + S O). (* 2 + 1 = 3 *)

    
End Nat.







(** For the rest of the course we will use standard library natural numbers,
    which are defined the same way, but come with decimal notation;
    e.g. 0,1,2,3, etc are nats.*)

Print nat. (* Inductive nat : Set :=  O : nat | S : nat -> nat. *)
Compute (pred 3). (* ==> 2 *)

    


(* ################################################################# *)
(** * Lists. *)
Module List.
    Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.
    Check nil.
    Check cons.

    Definition natlist1 := cons nat 3 (cons nat 4 (nil nat)).
    (** The type arguments can be quite annoying, but luckily they are unnecessary,
        as they can be inferred from the other arguments. *)
    Definition natlist2 := cons _ 3 (cons _ 4 (nil _)).

    (** In fact, we can declare these arguments to be implicit always using the
        [Arguments] command. The non-implicit version can always be accessed with
        [@nil] and [@cons]. *)
    Arguments nil {A}.
    Arguments cons {A}.

    Definition natlist3 := cons 3 (cons 4 nil).
    Definition natlist4 := @cons nat 3 (cons 4 (@nil nat)).

    (** We will use notation for cons and nil to make it a bit nicer to write. *)
    Notation "[]" := nil.
    Notation "x :: l" := (cons x l).
    Notation "[ x ; y ; .. ; z ]" :=
        (cons x (cons y .. (cons z nil) ..)).

    Definition natlist5 := 3::4::[].
    Definition natlist6 := [3;4].

    Open Scope nat_scope.







    (** Append and length are very important functions. *)
  
    Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
      match l1 with
      | nil      => l2
      | cons h t => cons h (app t l2)
      end.

    Fixpoint length {X : Type} (l : list X) : nat :=
      match l with
      | nil => 0
      | cons _ l' => S (length l')
      end.




    (** We can of course write higher-order functions like [map]. *)
    Fixpoint map {A B : Type} (f : A -> B) (l : list A)
                : list B :=
        match l with
        | [] => []
        | a :: l' => f a :: map f l'
        end.

    (** We can construct anonymous functions using [fun x => ...]. *)
    Compute (map (fun x => pred x) [1;2;3;4]).
      (* = [0; 1; 2; 3] *)
End List.









(** We will use standard library lists for the rest of the course. *)
Require Import List.
Import ListNotations.
Open Scope list_scope.










(** ** Dependent types

    Coq's type system is founded on dependent types---types
    that can depend on values. 
    
    Consider, for example, the type of length-indexed lists. *)

    Inductive Vec (A : Type) : nat -> Type :=
    | vnil : Vec A 0
    | vcons : forall {n : nat},
                A ->
                Vec A n ->
                Vec A (S n).
Check Vec.
Check vcons.










    Check vnil. (* forall A, Vec A 0 *)
    Check vcons. (* forall (A : Type) (n : nat), A -> Vec A n -> Vec A (S n) *)

    (* Make these arguments implicit. *)
    Arguments vnil {A}.
    Arguments vcons {A n}.

    Check (vcons 3 (vcons 4 vnil)).







    Fixpoint vappend {A : Type} {n1 n2 : nat}
                     (ls1 : Vec A n1) (ls2 : Vec A n2)
                     : Vec A (n1 + n2) :=
        match ls1 with
        
        | vnil => (*n1 = 0*)
                    (* n1 + n2 = 0 + n2 = n2 *)
                    ls2

        | @vcons _ n1' a ls1' => 
                    (* n1 = S n1' *)
                    (* n1 + n2 = S n1' + n2 =def S (n1' + n2)*)
                vcons a (vappend ls1' ls2 : Vec A (n1' + n2))
        end.
    
    Eval cbv in (vappend (vcons 3 vnil) (vcons 5 (vcons 4 vnil))).




    

    Fixpoint to_list {A : Type} {n : nat}
                     (ls : Vec A n)
                     : list A :=
        match ls with
        | vnil => nil
        | vcons a ls' => cons a (to_list ls')
        end.











    
    (** ** Propositions as types
    
        What is a dependent type, really? Let's think outside the box.
    
        Here is an inductive type with two parameters [x : foo a b].

        It has only one constructor, though, and only for the same argument
        [foo_same a : foo a a].
    *)
    Inductive foo {A : Type} : A -> A -> Type :=
    | foo_same (a : A) : foo a a.











    (** Since the only term of type [foo a b] is a constructor [foo_same a],
        the existance of that term is a _proof_ that [a=b]. *)

    Definition three : nat := 3.
    Definition foo_2_plus_1 : @foo nat (2+1) 3 :=
        foo_same 3.
 
    Require Import Program.
    Program Definition foo_commutativity {A : Set}
                    (a b : A) (pf : foo a b) : foo b a :=
      match pf with
      | foo_same a => (*aka b=a*) foo_same a
      end.
    
    (** Of course, in the standard library, this data type is called [eq],
        and it comes with notation [a = b]. *)
    Print eq.
    
    Fixpoint to_list_length {A : Type} {n : nat}
                            (ls : Vec A n)
             : length (to_list ls) = n :=
    match ls with
    | vnil => (*n=0*)
                (* length (to_list vnil) = 0 *)
                (* length nil = 0 *)
                (* 0 = 0 *)
                eq_refl 0

    | @vcons _ n' a ls' => (* n = S n' *)
                (* length (to_list (vcons a ls')) = S n' *)
                (* length (cons a (to_list ls')) = S n' *)
                (* S (length (to_list ls')) = S n' *)
                (* to_list_length ls'
                   : length (to_list ls') = n' *)
                (* final goal: S (length (to_list ls')) = S (length (to_list ls'))*)
                match to_list_length ls' with 
                | eq_refl _ =>
                eq_refl _
                end
    end.

    
    (** What a hassle! But there is a better way--tactics! *)
    Definition to_list_length' :
        forall (A : Type) (n : nat) (ls : Vec A n),
            length (to_list ls) = n.
    Proof.
        intros A n ls. (* refine (fun A n ls => _) *)

        induction ls as [ | n' a ls' IH]. (* Fixpoint + match ls with ... end *)
        { simpl. (* unfold definitions *)
          apply eq_refl.
        }
        { simpl.
          rewrite IH. (* transitivity of eq *)
          reflexivity. (* apply eq_refl *)
        }
    Defined.
    Print to_list_length'.
    Compute (to_list_length' nat 1 (vcons 2 vnil)).

    (** Underneath, this is still a term of the given type. *)
    Print to_list_length'.

    






    
    (** Another example: similar to vappend.
    
    [Theorem] or [Lemma] is the same as [Definition]. *)
    Theorem append_length :
        forall (A : Type) (ls1 ls2 : list A),
            length (ls1 ++ ls2) = length ls1 + length ls2.
    Proof.
        Locate "++". Print app.
        (** We essentially already did this with vappend, but let's do it as
            a theorem now. Instead of _recursion_, we will use _induction_
            (they are two views of the same thing). *)
        Check list_ind.
        intros A. (* Move [A] to hypothesis *)


        set (P := fun (ls1 : list A) => forall (ls2 : list A),
                    length (ls1 ++ ls2) = length ls1 + length ls2).
        change (forall ls1, P ls1).
        apply (@list_ind A P).
            (* will generate two subgoals for the two missing arguments *)
        * (* P nil *)
          unfold P.
          intros ls2. simpl. reflexivity.
        * (* P (a :: l) *)
          intros a l IH.
          unfold P in *.
          intros ls2. simpl.
          rewrite IH.
          reflexivity.
    Qed.
    (** It isn't necessary to define P in this way; using [apply list_ind] will
        give you the same result, or, more commonly, [induction ls1]. *)
    Print append_length.

    (** Let's try another, even simpler, example. *)

    Theorem add_0_r : forall n:nat, n + 0 = n.
    Proof.
      intros n. induction n as [| n' IHn'].
      - (* n = 0 *) simpl. reflexivity.
      - Print plus. Print Nat.add.
       (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
    Qed.

    (** If we look at the type of [eq] again, we see that unlike [foo], the
        return type is called [Prop], not [Type]. *)
    Print foo.
    Print eq.
    (** [Prop], [Type], and [Set] are all examples of *universes*.
        All terms have types in Coq. All types are themselves terms.
        Therefore, all types have other types---specifically, all types
        live in a universe. Simple types like [nat] and [bool] have type [Set].
        Simple proof types like [a = b] have type [Prop].
        More complicated types like [list Type] have kind [Type].

        Really, every instance of [Type] has an implicit natural number argument---
        [Type 0 : Type 1], [Type 3 : Type 4], etc. This ensures that no type
        is a member of itself. Roughly, [Set] and [Prop] are equivalent to
        [Type 0], and [list (Type n) : Type (S n)].
        
        A lot more can be said about universes, but we won't worry about it for now.*)







(* ================================================================= *)
(** ** Inductive predicates *)

(** While [eq] is extremely widely used, we can also define custom predicates
    using [Inductive] definitions. *)
Module le.

    
    Inductive le : nat -> nat -> Prop :=
    | le_O : forall n, le O n
    | le_S : forall m n,
             le m n ->
             le (S m) (S n).




    Theorem le_n_S : forall n, le n (S n).
    Proof.
        induction n as [ | n'].
        * apply le_O.
        * apply le_S. refine IHn'.
    Qed.








    Lemma le_antisymmetric : forall m n,
          le m n ->
          le n m ->
          m = n.
    
    Proof.
        (* To prove this lemma, we want to do induction on the relation [le n1 n2] itself. *)
        Check le_ind.
        (*
            le_ind
                : forall P : nat -> nat -> Prop,
                (forall n : nat, P 0 n) ->
                (forall m n : nat, le m n -> P m n -> P (S m) (S n)) ->
                forall n n0 : nat, le n n0 -> P n n0
            *)
        set (P := fun m n => (le n m -> m = n)).
        change (forall m n, le m n -> P m n).
        apply (@le_ind P).

        * unfold P. intros n H0.
          inversion H0.

              (* If we use the [inversion] tactic on [H], it is sort of like [destruct]---
                 it will look at all the ways [H] could possibly exist based on its 
                 type, and deconstruct it. 
                 If there are multiple ways [H] could have been constructed, it will give us
                 multiple subgoals. However, in this case there is only one possible
                 way. *)
              (* Now we know n = 0, so our goal is trivial. *)
            reflexivity.
        * unfold P.
            intros m n
                   Hle (* m <= n *)
                   IH  (* n <= m -> m = n *)
                   H   (* S n <= S m *).





              (* Now, S n <= S m implies n <= m. Why? Again, the only terms
                 of the form [le (S n) (S m)] are those formed by the [le_S] constructor. *)
            inversion H as [n' | m' n' Hmn'].


              (* Unfortunately, inversion introduces fresh variables ([m'] and [n'] above)
                 even though they are equal to our original [m] and [n]. As a result,
                 we will often use [subst] immediately following [inversion] to eliminate
                 these extra variables. All [subst] does is look for hypothesis of the form
                 [x=e] or [e=x] and replace all occurrences of [x] with [e]. *)
            subst.



              (* Now [Hmn' : le n m] *)
            rewrite IH.
            + reflexivity.
            + exact Hmn'.
    Qed.
    Print le_antisymmetric.










    Lemma le_trans : forall n1 n2 n3,
          le n1 n2 ->
          le n2 n3 ->
          le n1 n3.
    
      (* To prove this lemma, we want to do induction on the relation [le n1 n2] itself.
         However, we don't quite have the right form to apply le_ind directly.
         Let's do some rearranging to get it into the right form. *)
      intros n1 n2 n3 H12 H23.
      generalize dependent n3.
      revert n1 n2 H12.
      set (P := fun n1 n2 => forall n3, le n2 n3 -> le n1 n3).
      change (forall n1 n2, le n1 n2 -> P n1 n2).
      (* Instead of [apply le_ind], we can introduce the hypothesis and 
         call [induction] on the hypothesis. *)
      intros n1 n2 H. unfold P.
      induction H as [n1 | n1 n2 H12 IH].
      2:{
        intros n3 H23.
        (* Because S n2 <= n3, it must be the case that [n3=S n3'] such that
           [n2 <= n3']. *)
        inversion H23 as [n2' | n2' n3' H23']. subst.
        apply le_S.
        (* Now we can apply IHH12, because it's true [forall n3]! *)
        apply IH.
        exact H23'.
      }
      1:{ intros n3 H23. apply le_O. }
    Qed.

    (* Now, even though we didn't have to [apply le_ind] directly, it's still
       useful to think this way because it generates the correct induction
       hypothesis. For example, we can try to restart without this restructing. *)
    
    Lemma le_trans_failure : forall n1 n2 n3,
       le n1 n2 ->
       le n2 n3 ->
       le n1 n3.
    Proof.
      intros n1 n2 n3 H12 H23.
      induction H12 as [n1 | n1 n2 H12'].
      2:{
        (* We expect n3 to be of the form Sn3' *)
        inversion H23 as [n2' | n2' n3' H23']. 
        subst.
        apply le_S.
        (* Now we are stuck, because the induction hypothesis 
           is only valid for [S n3'], but we need it
           for [n3'] itself! *)
    Abort.

End le.

