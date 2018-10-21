Inductive day: Type:=
    | monday
    | tuesday
    | wednesday
    | thursday
    | friday
    | saturday
    | sunday.

Definition next_weekday(d:day) : day :=
  match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
    end.

Inductive bool : Type :=
    | true
    | false.

Definition negb (b:bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

Definition andb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => b2
    | false => false
    end.

Definition orb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => true
    | false => b2
    end.

Example test_orb1 :(orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2:(orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3:(orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4:(orb true true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* nandb *)
Definition nandb (b1:bool) (b2:bool) : bool :=
  (negb (andb b1 b2)).

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
    (andb (andb b1 b2) b3).

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Inductive rgb : Type := 
    | red
    | green
    | blue.

Inductive color : Type :=
    | black
    | white
    | primary (p: rgb).

Definition monochrome(c:color) : bool :=
    match c with
    | black => true
    | white => true
    | primary q => false
    end.

Definition isred (c:color) : bool :=
    match c with
    | black => false
    | white => false
    | primary red => true
    | primary _ => false
    end.

Inductive bit : Type :=
    | B0
    | B1.

Inductive nybble : Type :=
    | bits (b0 b1 b2 b3 : bit).

Definition all_zero(nb:nybble):bool :=
    match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
    end.

Module NatPlayground.

Inductive nat : Type :=
    | O
    | S (n:nat).

Definition pred(n:nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

End NatPlayground.

Definition minustwo(n:nat): nat :=
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.

Fixpoint evenb (n:nat): bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
    end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n:nat) (m:nat) : nat :=
    match n with
     | O => m
     | S n' => S (plus n' m)
    end.

Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

Example test_mult1 : (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat :=
    match n,m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
    end.

End NatPlayground2.

Fixpoint exp (base power: nat) : nat :=
    match power with
    | O => S O
    | S p => mult base (exp base p)
    end.

(*factorial*)

Fixpoint factorial (n:nat) : nat :=
    match n with
    | O => S O
    | S p => mult n (factorial p)
    end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                    (at level 50, left associativity)
                    : nat_scope.
Notation "x - y" := (minus x y)
                    (at level 50, left associativity)
                    : nat_scope.
Notation "x * y" := (mult x y)
                    (at level 40, left associativity)
                    : nat_scope.

Fixpoint eqb (n m : nat) : bool :=
    match n with
    | O => match m with
           | O => true
           | S m' => false
           end
    | S n' => match m with
              | O => false
              | S m' => eqb n' m'
              end
    end.

Fixpoint leb (n m : nat) : bool :=
    match n with
    | O => true
    | S n' => match m with
              | O => false
              | S m' => leb n' m'
              end
    end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation " x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb4: (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

(*ltb*)
Definition ltb (n m : nat) : bool :=
    (andb (leb n m) (negb (leb m n))).
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n: forall n: nat, 0 + n = n.
Proof.
    intros n. simpl. reflexivity.
Qed.

Theorem plus_1_l: forall n: nat, 1 + n = S n.
Proof.
    intros n. reflexivity.
Qed.

Theorem mult_0_l: forall n: nat, 0 * n = 0 .
Proof.
    intros n. reflexivity.
Qed.

Theorem plus_id_example: 
    forall n m: nat,
    n = m -> n + n = m + m.
Proof.
    intros n m.
    intros H.
    rewrite -> H.
    reflexivity.
Qed.

(*plus_id_exercise*)
Theorem plus_id_exercise :
    forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
    intros n m o.
    intros X Y.
    rewrite -> X.
    rewrite -> Y.
    reflexivity.
Qed.

Theorem mult_0_plus:
    forall n m : nat,
    (0 + n) * m = n * m.
Proof.
    intros n m.
    rewrite -> plus_O_n.
    reflexivity.
Qed.

Theorem mult_S_1:
    forall n m: nat,
    m = S n -> m * (1 + n) = m * m.
Proof.
    intros n m.
    intros H.
    rewrite -> H.
    reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry:
    forall n:nat, (n + 1) =? 0 = false.
Proof.
    intros n.
    simpl.
Abort.

Theorem plus_1_neq_0:
    forall n:nat, (n + 1) =? 0 = false.
Proof.
    intros n. destruct n as [| n'] eqn:E.
    - reflexivity.
    - reflexivity.
Qed.

Theorem negb_involutive: forall b:bool, negb (negb b) = b.
Proof.
    intros b. destruct b eqn:E.
    - reflexivity.
    - reflexivity.
Qed.

Theorem andb_commutative: forall b c:bool, andb b c = andb c b.
Proof.
    intros b c. destruct b eqn:Eb.
    - destruct c eqn:Ec.
      + reflexivity.
      + reflexivity.
    - destruct c eqn:Ec.
      + reflexivity.
      + reflexivity.
Qed.

Theorem andb_commutative': forall b c:bool, andb b c = andb c b.
Proof.
    intros b c. destruct b eqn:Eb.
    { destruct c eqn:Ec.
      { reflexivity. }
      { reflexivity. }
    }
    { destruct c eqn:Ec.
      { reflexivity. }
      { reflexivity. }
    }
Qed.

Theorem andb3_exchange:
    forall b c d,
    andb (andb b c) d = andb (andb b d) c.
    Proof.
    intros b c d. destruct b eqn:Eb.
    - destruct c eqn:Ec.
      { destruct d eqn:Ed.
        - reflexivity.
        - reflexivity. }
      { destruct d eqn:Ed.
        - reflexivity.
        - reflexivity. }
    - destruct c eqn:Ec.
      { destruct d eqn:Ed.
        - reflexivity.
        - reflexivity. }
      { destruct d eqn:Ed.
        - reflexivity.
        - reflexivity. }
    Qed.

Theorem plus_1_neq_0': forall n: nat, (n + 1) =? 0 = false .
Proof.
    intros [| n].
    - reflexivity.
    - reflexivity.
Qed.

Theorem andb_commutative'' :
    forall b c, andb b c = andb c b.
Proof.
    intros [] [].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
Qed.

(*andb_true_elim2*)
Theorem andb_true_elim2:
    forall b c: bool, andb b c = true -> c = true.
Proof.
    intros [] [].
    - reflexivity.
    - simpl. intros H. rewrite -> H. reflexivity.
    - reflexivity.
    - simpl. intros H. rewrite -> H. reflexivity.
Qed.

(*zero_nbeq_plus_1*)
Theorem zero_nbeq_plus_1:
    forall n:nat, 0 =? (n + 1) = false.
Proof.
    intros [| n'].
    - reflexivity.
    - reflexivity.
Qed.

Fixpoint plus' (n:nat) (m:nat) :nat := 
    match n with
    | O => m
    | S n' => S (plus' n' m)
    end.

(*decreasing*)

(*indentity_fn_applied_twice*)
Theorem indentity_fn_applied_twice: 
    forall (f: bool -> bool),
    (forall (x:bool), f x = x) -> forall (b:bool), f (f b) = b.
Proof.
    intros f H b. 
    rewrite -> H. rewrite -> H. 
    reflexivity.
Qed.

Theorem negation_fn_applied_twice: 
forall (f: bool -> bool),
    (forall (x:bool), f x = negb x) -> forall (b:bool), f (f b) = b.
Proof.
    intros f H b. 
    rewrite -> H. rewrite -> H. 
    rewrite -> negb_involutive.
    reflexivity.
Qed.

Theorem andb_eq_orb: 
    forall (b c : bool),
    (andb b c = orb b c) -> b = c.
Proof.
    intros [] [].
    - reflexivity.
    - simpl. intros H. rewrite -> H. reflexivity.
    - simpl. intros H. rewrite -> H. reflexivity.
    - reflexivity.
Qed.

Inductive bin : Type :=
    | Z
    | A (n:bin)
    | B (n:bin).
    
Fixpoint incr (m:bin) : bin :=
    match m with
    | Z => B Z
    | B m' => A (incr m')
    | A m' => B m'
    end.

Fixpoint bin_to_nat (m:bin) : nat :=
    match m with
    | Z => O
    | A m' => 2 * (bin_to_nat m')
    | B m' => 1 + 2 * (bin_to_nat m')
    end.

Example test_bin_incr1: (bin_to_nat (incr (incr (incr Z)))) = 3.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2: (bin_to_nat (incr Z)) = 1.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3: (bin_to_nat (incr ((A (B (B Z)))))) = 7.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr4: (bin_to_nat (incr (A (A (A (B Z)))))) = 9.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr5: (bin_to_nat (incr (incr (incr (incr (incr ((A (A (A (B Z))))))))))) = 13.
Proof. simpl. reflexivity. Qed.