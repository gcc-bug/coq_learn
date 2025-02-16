Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
Inductive bool : Type :=
  | true
  | false.
Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.
Compute (next_weekday (next_weekday friday)).
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

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
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* ! exercise *)
Module exercise1group .
  (* !exercise 1.1 *)
  (* Definition nandb (b1:bool) (b2:bool) : bool :=
    match b2 with 
    | false => true
    | true => (negb b1)
    end. *)
  Definition nandb (b1:bool) (b2:bool) : bool :=
    (negb (andb b1 b2)).
    (* todo: 如何直接返回 negb (andb b1 b2). *)
  Example test_nandb1: (nandb true false) = true.
  Proof. simpl. reflexivity. Qed.
  Example test_nandb2: (nandb false false) = true.
  Proof. simpl. reflexivity. Qed.
  Example test_nandb3: (nandb false true) = true.
  Proof. simpl. reflexivity. Qed.
  Example test_nandb4: (nandb true true) = false.
  Proof. simpl. reflexivity. Qed.
  (* ! exercise 1.2 *)
  Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool := 
  match b1 with 
  | true => (andb b2 b3)
  | false => false
  end .
  Example test_andb31: (andb3 true true true) = true.
  Proof. simpl. reflexivity. Qed.
  Example test_andb32: (andb3 false true true) = false.
  Proof. simpl. reflexivity. Qed.
  Example test_andb33: (andb3 true false true) = false.
  Proof. simpl. reflexivity. Qed.
  Example test_andb34: (andb3 true true false) = false.
  Proof. simpl. reflexivity. Qed.
End exercise1group.
Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.
Module Playground.
  Definition b : rgb := blue.
End Playground.
Definition b : bool := true.
Check Playground.b : rgb.
Check b : bool.

Module TuplePlayground.
  Inductive bit : Type :=
    | B0
    | B1.
  Inductive nybble : Type :=
    | bits (b0 b1 b2 b3 : bit).
  Check (bits B1 B0 B1 B0)
    : nybble.
  Definition all_zero (nb : nybble) : bool :=
    match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
    end.
  Compute (all_zero (bits B1 B0 B1 B0)).
  (* ===> false : bool *)
  Compute (all_zero (bits B0 B0 B0 B0)).
  (* ===> true : bool *)
End TuplePlayground.

Module NatPlayground.
  Inductive nat : Type :=
    | O
    | S (n : nat).
  Check (S(S O))
  : nat.

  Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

  Compute (pred (pred (S(S O)))).

  
  Check (S (S (S (S O)))).
  Check 4.

  Fixpoint even (n:nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n') => even n'
    end.

  Definition odd (n:nat) : bool :=
    negb (even n).
  Compute (even (S(S (S(S O))))).

  Example test_odd1: odd (S O) = true.
  Proof. simpl. reflexivity. Qed.
  Example test_odd2: odd (S(S (S(S O)))) = false.
  Proof. simpl. reflexivity. Qed.

End NatPlayground.

Module NatPlayground2.
  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.
  
  Compute (plus 3 2).

  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.
  Example test_mult1: (mult 3 3) = 9.
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus (n m:nat) : nat :=
    match n, m with
    | O , _ => O
    | _ , O => n
    | S n', S m' => minus n' m'
    end.
  Compute (minus 4 5).

  Fixpoint exp (base power : nat) : nat :=
    match power with
    | O => S O
    | S p => mult base (exp base p)
    end.
End NatPlayground2.

Module exercise2group.
  Fixpoint factorial (n : nat) : nat := 
    match n with
    | O => S O
    | S n' => (mult n (factorial(n')))
    end.

  Compute factorial (5).
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
  Check ((0 + 1) + 1).

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

  Compute (eqb 5000 5000).
  (* 5001 is too large for nat *)
  (* Compute (eqb 5001 5001). *)
End exercise2group.

Module exercise3group.
  Fixpoint ltb (n m : nat) : bool:=
    match m with 
    | O => false
    | S m' => match n with
      | O => true
      | S n' => ltb n' m'  
      end
    end.
  Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
  Example test_ltb1: (ltb 2 2) = false.
  Proof. simpl. reflexivity. Qed.
  Example test_ltb2: (ltb 2 4) = true.
  Proof. simpl. reflexivity. Qed.
  Example test_ltb3: (ltb 4 2) = false.
  Proof. simpl. reflexivity. Qed.
End exercise3group.

Theorem plus_O_n : forall n : nat, 0 + n = n.
(* Proof.
  intros n. simpl. reflexivity. Qed. *)

Proof.
  intros n. reflexivity. Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, mult 0 n = 0.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite H.
  reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros G.
  rewrite H.
  rewrite G.
  reflexivity. 
  Qed.


Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.

Check mult_n_O.
Check mult_n_Sm.
Check plus_O_n.
Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros n.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  (* rewrite <- plus_O_n. *)
  (* or *)
  rewrite <- plus_O_n.
  reflexivity.
  Qed.
  (* Todo: rewrite的重写逻辑 *)
Check mult_n_1.

Fixpoint ltb (n m : nat) : bool:=
    match m with 
    | O => false
    | S m' => match n with
      | O => true
      | S n' => ltb n' m'  
      end
    end.

Theorem plus_1_neq_0 : forall n : nat,
  (ltb (n + 1)  0) = false.
Proof.
  intros n. 
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. 
  Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b eqn: Eb.
  - intros H.
    rewrite <- H.
    reflexivity.
  - destruct c eqn: Ec.
    + intros H.
      rewrite <- H.
      reflexivity.
    + intros H.
      rewrite <- H.
      reflexivity.
  Qed.
Theorem plus_1_neq_0' : forall n : nat,
  (ltb (n + 1)  0) = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Check 0 <= 1.
Definition bgr (n m: nat): bool:= 
  ltb m n.
Theorem zero_nbeq_plus_1 : forall n : nat,
  (bgr 0 (n + 1)) = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
(* Proof.
  intros f.
  intros H.
  intros [].
  - rewrite <- H.
    rewrite <- H.
    reflexivity.
  - rewrite <- H.
    rewrite <- H.
    reflexivity.
  Qed. *)

Proof.
  intros f.
  intros H.
  intros b.
  rewrite H.
  rewrite H.
  reflexivity.
  Qed.


Lemma  andb_f_t: 
  andb false true = false.
Proof.
  reflexivity.
Qed.

Lemma andb_t_f : 
  andb true false = false.
Proof. 
  reflexivity. 
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  intros H.
  destruct b eqn: Eb.
  - destruct c eqn: Ec.
    + reflexivity.
    + rewrite <- andb_t_f. 
      rewrite -> H.
      reflexivity.
  - destruct c eqn: Ec.
    + rewrite <- andb_f_t.
      rewrite -> H.
      reflexivity.
    + reflexivity.
Qed.

(* ! exercise 3 *)
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).
Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 (n) => B1 (n)
  | B1 (n) => B0 (incr(n))
  end. 
Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B0 (n) => (mult (S(S O)) (bin_to_nat(n)))
  | B1 (n) => (plus 1 (mult 2 (bin_to_nat(n))))
  end.
Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.
Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.
Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.