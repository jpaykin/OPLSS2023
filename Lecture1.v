(** * Basics: Functional Programming in Coq *)

(** * Lecture 1

Coq consists of a
    dependently-typed
    functional programming langauge
as well as an
    interactive therorem prover.
*)

(* ================================================================= *)
(** ** A functional programming langauge *)

Require Import Coq.Program.Equality.

Module Nat.
    (** Unary natural numbers are either
        - 0 (the letter "O")
        - the successor of a natural number [S n]
    *)
    Inductive nat : Set :=
    | O : nat 
    | S (n : nat) : nat.

    (** Let's look at this in a little more detail.

        An [Inductive] definition does two things:

        - It defines a set of new _constructors_, e.g., [O] and
          [S] are constructors.

        - It groups them into a new named type, e.g. [nat].

        _Constructor expressions_ are formed by applying a constructor
        to zero or more other constructors or constructor expressions,
        obeying the declared number and types of the constructor arguments.
        E.g., [S (S O)]
    *)

    (** We can check the types of terms we have defined, or print out definitions,
        using the [Check] and [Print] commands. *)
    Check nat. (* : Set *)
    Check S. (* : nat -> nat *)
    Print nat.

    (** We can define functions over natural numbers by case analysis. *)
    Definition pred (n : nat) : nat :=
        match n with
        | O => O
        | S n' => n'
        end.

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

    (** Critical point: this just defines a _representation_ of
        numbers -- a unary notation for writing them down.

        The names [O] and [S] are arbitrary. They are just two different
        "marks", with no intrinsic meaning.

        We could just as well represent numbers with different marks. *)

    
End Nat.

(** Coq provides a _module system_ to aid in organizing large
    developments.  We won't need most of its features,
    but one is useful: If we enclose a collection of declarations
    between [Module X] and [End X] markers, then, in the remainder of
    the file after the [End], these definitions are referred to by
    names like [X.foo] instead of just [foo].  We will use this
    feature to limit the scope of definitions, so that we are free to
    reuse names. *)

(** For the rest of the course we will use standard library natural numbers,
    which are defined the same way, but come with decimal notation;
    e.g. 0,1,2,3, etc are nats.*)

Print nat. (* Inductive nat : Set :=  O : nat | S : nat -> nat. *)
Compute (pred 3). (* ==> 2 *)

(* ================================================================= *)
(** ** Exercises *)

    (** **** Exercise: 1 star, standard (factorial) *)
    (** Recall the standard mathematical factorial function:
    <<
          factorial(0)  =  1
          factorial(n)  =  n * factorial(n-1)     (if n>0)
    >>
        Translate this into Coq.

        Feel free to use [m * n] aka [Nat.mul m n] for multiplication of natural numbers
        (defined in the standard library).

        Make sure you put a [:=] between the header we've given you and
        your definition.  If you see an error like "The reference
        factorial was not found in the current environment," it means
        you've forgotten the [:=]. *)
    Print Nat.mul.

    Fixpoint factorial (n:nat) : nat
      (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

    (** Uncomment the lines below to check some unit tests. *)
    (*
    Example test_factorial1:          (factorial 3) = 6.
    Proof. simpl. reflexivity.  Qed.
    Example test_factorial2:          (factorial 5) = (mult 10 12).
    Proof. simpl. reflexivity.  Qed.
    *)
    (** [] *)
    
        (** **** Exercise: 1 star, standard (eqb) *)
    (** The [eqb] function tests natural numbers for [eq]uality,
        yielding a [b]oolean. A boolean is an inductively-defined definition
        with two constructors: [true] and [false]. *)

        Print bool. (* Inductive bool : Set :=  true : bool | false : bool. *)

    (** Define [eqb] using [Fixpoint] and [match] notation. You may have to use
        nested match statements. *)

        Fixpoint eqb (n m : nat) : bool
        (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
      
      Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
      
      (** Uncomment the below unit tests: *)
      (*
      Example test_eqb0:             (eqb 0 0) = true.
      Proof. simpl. reflexivity.  Qed.
      Example test_eqb1:             (eqb 2 2) = true.
      Proof. simpl. reflexivity.  Qed.
      Example test_eqb2:             (eqb 2 4) = false.
      Proof. simpl. reflexivity.  Qed.
      Example test_eqb3:             (eqb 4 2) = false.
      Proof. simpl. reflexivity.  Qed.
      *)
      (** [] *)
      

        (** ** Binary Numerals *)

    (** **** Exercise: 3 stars, standard (binary) *)
    (** We can generalize our unary representation of natural numbers to
        the more efficient binary representation by treating a binary
        number as a sequence of constructors [B0] and [B1] (representing 0s
        and 1s), terminated by a [Z]. For comparison, in the unary
        representation, a number is a sequence of [S] constructors terminated
        by an [O].

        For example:
    <<
            decimal               binary                          unary
              0                       Z                              O
              1                    B1 Z                            S O
              2                B0 (B1 Z)                        S (S O)
              3                B1 (B1 Z)                     S (S (S O))
              4            B0 (B0 (B1 Z))                 S (S (S (S O)))
              5            B1 (B0 (B1 Z))              S (S (S (S (S O))))
              6            B0 (B1 (B1 Z))           S (S (S (S (S (S O)))))
              7            B1 (B1 (B1 Z))        S (S (S (S (S (S (S O))))))
              8        B0 (B0 (B0 (B1 Z)))    S (S (S (S (S (S (S (S O)))))))
    >>
        Note that the low-order bit is on the left and the high-order bit
        is on the right -- the opposite of the way binary numbers are
        usually written.  This choice makes them easier to manipulate. *)

    Inductive bin : Type :=
    | Z
    | B0 (n : bin)
    | B1 (n : bin).

    (** Complete the definitions below of an increment function [incr]
      for binary numbers, and a function [bin_to_nat] to convert
      binary numbers to unary numbers. *)

    Fixpoint incr (m:bin) : bin
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

    Fixpoint bin_to_nat (m:bin) : nat
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

    (** The following "unit tests" of your increment and binary-to-unary
      functions should pass after you have defined those functions correctly.
      Of course, unit tests don't fully demonstrate the correctness of
      your functions!  We'll return to that thought at the end of the
      next chapter. *)

    (*
    Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
    Proof. reflexivity.  Qed.

    Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
    Proof. reflexivity.  Qed.

    Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
    Proof. reflexivity.  Qed.

    Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
    Proof. reflexivity.  Qed.

    Example test_bin_incr5 :
          bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
    Proof. reflexivity.  Qed.

    Example test_bin_incr6 :
          bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
    Proof. reflexivity.  Qed.
    *)

    (** [] *)

    
(* ################################################################# *)
(** * Lists. *)
Module List.
    Inductive list (A : Type) : Type :=
    | nil : list A
    | cons : A -> list A -> list A.

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
    Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).

    Definition natlist5 := 3::4::[].
    Definition natlist6 := [3;4].

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
    Fixpoint map {A B : Type} (f : A -> B) (l : list A) : list B :=
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

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** **** Exercise: 2 stars, standard, especially useful (nonzeros)

    Complete the definition of [nonzeros] below. Have a look at the tests
    to understand what it should do. *)

    Fixpoint nonzeros (l:list nat) : list nat
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
  
  Example test_nonzeros:
    nonzeros [0;1;0;2;3;0;0] = [1;2;3].
    (* FILL IN HERE *) Admitted.
  
  (** [] *)



(** ** Dependent types

    Coq's type system is founded on dependent types---types
    that can depend on values. 
    
    Consider, for example, the type of length-indexed lists. *)

    Inductive Vec (A : Type) : nat -> Type :=
    | vnil : Vec A 0
    | vcons {n : nat} (a : A) (v : Vec A n) : Vec A (S n).
    Check vnil. (* forall A, Vec A 0 *)
    Check vcons. (* forall A n, A -> Vec A n -> Vec A (S n) *)

    (* Make these arguments implicit. *)
    Arguments vnil {A}.
    Arguments vcons {A n}.

    Fixpoint vappend {A : Type} {n1 n2 : nat}
                     (ls1 : Vec A n1) (ls2 : Vec A n2) : Vec A (n1 + n2) :=
        match ls1 with
        | vnil => (* n1=0, n1 + n2 = n2 *)
          ls2
        | vcons a ls1' => (* n1 = S n1', n1 + n2 = S (n1' + n2) *)
          vcons a (vappend ls1' ls2)
        end.
    
    Compute (vappend (vcons 3 vnil) (vcons 5 (vcons 4 vnil))).
    

    Fixpoint to_list {A : Type} {n : nat}
                     (ls : Vec A n)
                     : list A :=
        match ls with
        | vnil => nil
        | vcons a ls' => cons a (to_list ls')
        end.

(** **** Exercise: 2 stars, standard, especially useful (from_list)

    Define a function that takes a list to a Vector, where the length of the
    vector is given by [length l]. *)

    Fixpoint from_list {A : Type} (l:list A) : Vec A (length l)
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
  
  Example to_from_list:
    to_list (from_list [3;4;2]) = [3;4;2].
    (* FILL IN HERE *) Admitted.
  
  (** [] *)
    
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

    Definition foo_2_plus_1 : foo (2+1) 3 := foo_same 3.

    Definition foo_commutativity {A : Set} (a b : A) (pf : foo a b) : foo b a :=
      match pf with
      | foo_same a => foo_same a
      end.
    
    (** Of course, in the standard library, this data type is called [eq],
        and it comes with notation [a = b]. *)
    Print eq.
    
    Fixpoint to_list_length {A : Type} {n : nat} (ls : Vec A n)
             : length (to_list ls) = n :=
    match ls with
    | vnil => (* n = 0, to_list ls = nil *) eq_refl
    | vcons a ls' =>
      (* n = S n' *)
      (* to_list ls = a :: to_list ls' *)
      (* to_list_length ls' : eq (length (to_list ls')) n' *)
      (* WTS: eq (length (to_list (vcons a ls'))) (S n')
                (length (cons a ls'))            (S n')
                (S (length ls'))                 (S n')
      *)
      match to_list_length ls' with
      | eq_refl _ => eq_refl _
      end
    end.
    
    (** What a hassle! But there is a better way--tactics! *)
    Definition to_list_length' : forall (A : Type) (n : nat) (ls : Vec A n),
                                 length (to_list ls) = n.
    Proof.
        intros A n ls. (* refine (fun A n ls => _) *)
        induction ls. (* Fixpoint + match ls with ... end *)
        * simpl. (* unfold definitions *)
          apply eq_refl.
        * simpl.
          rewrite IHls. (* transitivity of eq *)
          reflexivity. (* apply eq_refl *)
    Qed.

    (** Underneath, this is still a term of the given type. *)
    Print to_list_length'.
    
    
    (** Another example: similar to vappend.
    
    [Theorem] or [Lemma] is the same as [Definition]. *)
    Theorem append_length : forall (A : Type) (ls1 ls2 : list A),
                            length (ls1 ++ ls2) = length ls1 + length ls2.
    Proof.
        Locate "++". Print app.
        (** We essentially already did this with vappend, but let's do it as
            a theorem now. Instead of _recursion_, we will use _induction_
            (they are two views of the same thing). *)
        Check list_rect.
        intros A. (* Move [A] to hypothesis *)
        set (P := fun ls1 => forall (ls2 : list A),
                    length (ls1 ++ ls2) = length ls1 + length ls2).
        change (forall ls1, P ls1).
        apply (@list_rect A P).
            (* will generate two subgoals for the two missing arguments *)
        * (* P nil *)
          unfold P.
          intros ls2. simpl. reflexivity.
        * (* P (a :: l) *)
          intros a l IH.
          unfold P in IH.
          unfold P.
          intros ls2. simpl.
          rewrite IH.
          reflexivity.
    Qed.
    (** It isn't necessary to define P in this way; using [apply list_rect] will
        give you the same result, or, more commonly, [induction ls1]. *)
    Print append_length.

    (** Let's try another, even simpler, example. *)

    Theorem add_0_r : forall n:nat, n + 0 = n.
    Proof.
      intros n. induction n as [| n' IHn'].
      - (* n = 0 *)    reflexivity.
      - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.
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

    (** The following definition says that there are two ways to
        show that one number is less than or equal to another: either
        observe that the first is 0, or, if the first has the
        form [S m], the second must have the form [S n] where m <= n. *)

    Inductive le : nat -> nat -> Prop :=
    | le_O (n : nat) : le O n
    | le_S (m n : nat) : le m n -> le (S m) (S n).

    Lemma le_n_S : forall n, le n (S n).
    (* WORKED IN CLASS *)
    Proof.
      (*  We can prove this lemma by induction on n *)
      induction n.
      * apply le_O.
      * apply le_S.
        exact IHn.
    Qed.
    
    Lemma le_asymmetric : forall m n,
          le m n ->
          le n m ->
          m = n.
    (* WORKED IN CLASS *)
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
      set (P := fun m n => le n m -> m = n).
      change (forall m n, le m n -> P m n).
      apply le_ind.
      * (* 0 <= n *)
        unfold P.
        intros n Hn0 (* n <= 0 *).
        (* Now, n <= 0 implies n = 0. Why? Well, because the only terms
           of the form [le n O] are those formed by the [le_O] constructor.
           This type of reasoning is called _inversion_. *)
        inversion Hn0.
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
    
    Lemma le_trans : forall n1 n2 n3,
          le n1 n2 ->
          le n2 n3 ->
          le n1 n3.
    Proof.
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
      induction H as [n1 | n1 n2 H12].
      * intros n3 H13. apply le_O.
      * intros n3 H23.
        (* Because S n2 <= n3, it must be the case that [n3=S n3'] such that
           [n2 <= n3']. *)
        inversion H23 as [n2' | n2' n3' H23']. subst.
        apply le_S.
        (* Now we can apply IHH12, because it's true [forall n3]! *)
        apply IHH12.
        exact H23'.
    Qed.

    (* Now, even though we didn't have to [apply le_ind] directly, it's still
       useful to think this way because it generates the correct induction
       hypothesis. For example, we can try to restart without this restructing. *)
    
    Lemma le_trans_failure : forall n1 n2 n3,
       le n1 n2 ->
       le n2 n3 ->
       le n1 n3.
    Proof.
      intros n1 n2 n3 H12.
      induction H12 as [n1 | n1 n2 H12'].
      * intros H13. apply le_O.
      * intros H23.
        inversion H23 as [n2' | n2' n3' H23']. (* We expect n3 to be of the form Sn3' *)
        subst.
        apply le_S.
        (* Now we are stuck, because the induction hypothesis is only valid
           for [S n3'], but we need it for [n3'] itself! *)
    Abort.
    

End le.

(* ================================================================= *)
(** ** Exercises *)

(** **** Exercise: 2 stars, standard, especially useful (basic_induction)

    Prove the following using induction. You might need previously
    proven results. *)

    Theorem mul_0_r : forall n:nat,
    n * 0 = 0.
  Proof.
    (* FILL IN HERE *) Admitted.
    
  Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
  Proof.
    (* FILL IN HERE *) Admitted.
  
  
  
  Theorem add_comm : forall n m : nat,
    n + m = m + n.
  Proof.
    (* FILL IN HERE *) Admitted.
  
    Theorem add_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
    Proof.
    (* FILL IN HERE *) Admitted.
        (** [] *)

    (** **** Exercise: 3 stars, standard, especially useful (mul_comm) *)
    (** Use [assert] to help prove [add_shuffle3].  You don't need to
        use induction yet. *)

    Theorem add_shuffle3 : forall n m p : nat,
    n + (m + p) = m + (n + p).
    Proof.
    (* FILL IN HERE *) Admitted.
        
    (** Now prove commutativity of multiplication.  You will probably want
    to look for (or define and prove) a "helper" theorem to be used in
    the proof of this one. Hint: what is [n * (1 + k)]? *)

    Theorem mul_comm : forall m n : nat,
    m * n = n * m.
    Proof.
    (* FILL IN HERE *) Admitted.
        (** [] *)


    (** **** Exercise: 2 stars, standard (double_plus) *)
    (** Consider the following function, which doubles its argument: *)

    Fixpoint double (n:nat) :=
      match n with
      | O => O
      | S n' => S (S (double n'))
      end.

    (** Use induction to prove this simple fact about [double]: *)

    Lemma double_plus : forall n, double n = n + n .
    Proof.
      (* FILL IN HERE *) Admitted.
    (** [] *)

    (** *** Nat to Bin and Back to Nat *)

    (** Earlier, we did some unit testing of [bin_to_nat], but we
      didn't prove its correctness. Now we'll do so. *)

    (** **** Exercise: 3 stars, standard, especially useful (binary_commute) *)
    (** Prove that the following diagram commutes:

    <<
                              incr
                bin ----------------------> bin
                |                           |
     bin_to_nat |                           |  bin_to_nat
                |                           |
                v                           v
                nat ----------------------> nat
                              S
    >>
      That is, incrementing a binary number and then converting it to
      a (unary) natural number yields the same result as first converting
      it to a natural number and then incrementing.

      If you want to change your previous definitions of [incr] or [bin_to_nat]
      to make the property easier to prove, feel free to do so! *)

    Theorem bin_to_nat_pres_incr : forall b : bin,
    bin_to_nat (incr b) = 1 + bin_to_nat b.
    Proof.
    (* FILL IN HERE *) Admitted.
    
    (** [] *)


    (** **** Exercise: 3 stars, standard (nat_bin_nat) *)

    (** Write a function to convert natural numbers to binary numbers. *)

    Fixpoint nat_to_bin (n:nat) : bin
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

    (** Prove that, if we start with any [nat], convert it to [bin], and
      convert it back, we get the same [nat] which we started with.

      Hint: This proof should go through smoothly using the previous
      exercise about [incr] as a lemma. If not, revisit your definitions
      of the functions involved and consider whether they are more
      complicated than necessary: the shape of a proof by induction will
      match the recursive structure of the program being verified, so
      make the recursions as simple as possible. *)

    Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
    Proof.
    (* FILL IN HERE *) Admitted.
    
    (** [] *)

(* ----------------------------------------------------------------- *)
(** *** Bin to Nat and Back to Bin (Advanced) *)

(** The opposite direction -- starting with a [bin], converting to [nat],
    then converting back to [bin] -- turns out to be problematic. That
    is, the following theorem does not hold. *)

Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Abort.

(** Let's explore why that theorem fails, and how to prove a modified
    version of it. We'll start with some lemmas that might seem
    unrelated, but will turn out to be relevant. *)

(** **** Exercise: 2 stars, advanced (double_bin) *)

(** Prove this lemma about [double], which we defined earlier in the
    chapter. *)

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
  (* FILL IN HERE *) Admitted.

(** Now define a similar doubling function for [bin]. *)

Definition double_bin (b:bin) : bin
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** Check that your function correctly doubles zero. *)

Example double_bin_zero : double_bin Z = Z.
(* FILL IN HERE *) Admitted.

(** Prove this lemma, which corresponds to [double_incr]. *)

Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** Let's return to our desired theorem: *)

Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Abort.

(** The theorem fails because there are some [bin] such that we won't
    necessarily get back to the _original_ [bin], but instead to an
    "equivalent" [bin].  (We deliberately leave that notion undefined
    here for you to think about.)

    Explain in a comment, below, why this failure occurs. Your
    explanation will not be graded, but it's important that you get it
    clear in your mind before going on to the next part. If you're
    stuck on this, think about alternative implementations of
    [double_bin] that might have failed to satisfy [double_bin_zero]
    yet otherwise seem correct. *)

(* FILL IN HERE *)

(** To solve that problem, we can introduce a _normalization_ function
    that selects the simplest [bin] out of all the equivalent
    [bin]. Then we can prove that the conversion from [bin] to [nat] and
    back again produces that normalized, simplest [bin]. *)

(** **** Exercise: 4 stars, advanced (bin_nat_bin) *)

(** Define [normalize]. You will need to keep its definition as simple
    as possible for later proofs to go smoothly. Do not use
    [bin_to_nat] or [nat_to_bin], but do use [double_bin].

    Hint: Structure the recursion such that it _always_ reaches the
    end of the [bin] and process each bit only once. Do not try to
    "look ahead" at future bits. *)

Fixpoint normalize (b:bin) : bin
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** It would be wise to do some [Example] proofs to check that your definition of
    [normalize] works the way you intend before you proceed. They won't be graded,
    but fill them in below. *)

(* FILL IN HERE *)

(** Finally, prove the main theorem. The inductive cases could be a
    bit tricky.

    Hint: Start by trying to prove the main statement, see where you
    get stuck, and see if you can find a lemma -- perhaps requiring
    its own inductive proof -- that will allow the main proof to make
    progress. We have one lemma for the [B0] case (which also makes 
    use of [double_incr_bin]) and another for the [B1] case. *)

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Subsequences *)
(** **** Exercise: 3 stars, advanced (subsequence)

    A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3]. *)

 Inductive subseq : list nat -> list nat -> Prop :=
 (* FILL IN HERE *)
 .
 
 Theorem subseq_refl : forall (l : list nat), subseq l l.
 Proof.
   (* FILL IN HERE *) Admitted.
 
 Theorem subseq_app : forall (l1 l2 l3 : list nat),
   subseq l1 l2 ->
   subseq l1 (l2 ++ l3).
 Proof.
   (* FILL IN HERE *) Admitted.
 
 Theorem subseq_trans : forall (l1 l2 l3 : list nat),
   subseq l1 l2 ->
   subseq l2 l3 ->
   subseq l1 l3.
 Proof.
   (* Hint: be careful about what you are doing induction on and which
      other things need to be generalized... *)
   (* FILL IN HERE *) Admitted.
    (** [] *)
 

(* 2023-06-25 21:10 *)
