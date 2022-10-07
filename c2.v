Print LoadPath. 
From Coq Require Import Nat .
Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.
Proof.
intros n. induction n as [| n' IHn'].
- (* n = 0 *) reflexivity.
- (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.
Check minus.
Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mul_0_r : forall n:nat,
    n * 0 = 0.
Proof.
    intros n.
    induction n as [| n' H].
    - simpl. reflexivity.
    - simpl. rewrite H. reflexivity.
Qed. 

Theorem plus_n_Sm : forall n m : nat,
    S (n + m) = n + (S m).
Proof.
    intros n m.
    induction n as [| n' H].
    - simpl. reflexivity.
    - simpl. rewrite H. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
    n + m = m + n.
Proof.
    intros n m.
    induction n as [| n' H].
    - simpl. induction m as [| m' Hm].
        + reflexivity.
        + simpl. rewrite <- Hm. reflexivity.
    - simpl. rewrite H. rewrite plus_n_Sm. reflexivity.
Qed.
Theorem add_assoc : forall n m p : nat,
n + (m + p) = (n + m) + p.
Proof.
    intros n m p .
    induction n as [| n' H].
    {simpl. reflexivity. }
    {simpl. rewrite H. reflexivity. }
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
Compute double 5.
Lemma double_plus : forall n, double n = n + n .
Proof.
    intros m.
    induction m as [| m' H].
    {simpl. reflexivity. }
    {simpl. rewrite H. rewrite plus_n_Sm. reflexivity. }
Qed.


Compute 5 =? 5.
Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
    intros n. induction n as [| n' H].
    {simpl. reflexivity. }
    {simpl. rewrite H. reflexivity. }
Qed.


Lemma negbb: forall b: bool,
    negb (negb b) = b.
Proof.
    intros [].
        - simpl. reflexivity.
        - simpl. reflexivity.
Qed. 
Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
    intros n.
    induction n as [| n' H].
    {simpl. reflexivity. }
    {rewrite H. simpl. rewrite negbb. reflexivity. }
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity. Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like add_comm should do the trick! *)
  rewrite add_comm.
  (* Doesn't work... Coq rewrites the wrong plus! :-( *)
Abort.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
    intros n m p.
    rewrite add_assoc. rewrite add_assoc. 
    assert (H: n + m = m + n).
        {rewrite add_comm. reflexivity. }
    rewrite H. reflexivity.
Qed.

Lemma mul_n_m_1 : forall m n: nat,
    m * S n = m + m * n.
Proof.
    intros m n.
    induction m as [| m' Hm'].
        - reflexivity.
        - simpl. rewrite Hm'. rewrite add_shuffle3. reflexivity.
Qed.   
Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
    intros m n.
    induction m as [| m' H].
        - rewrite mul_0_r. reflexivity.
        - simpl. rewrite  mul_n_m_1. rewrite H. reflexivity.
Qed.

Check leb.
Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
    intros n m p.
    intros H.
    induction p as [| p' Hp].
        - simpl. rewrite H. reflexivity.
        - simpl. rewrite Hp. reflexivity.
Qed.

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
  (* only induction? *)
Proof.
    intros n.
    induction n as [| n' IHn'].
        - simpl. reflexivity.
        - simpl. rewrite IHn'. reflexivity.  
Qed.
Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
  (* 三个都可以 *)
Proof.
    (* only simpl *)
    intros n.
    simpl.
    reflexivity.
Qed.
Theorem zero_neqb_S' : forall n:nat,
  0 =? (S n) = false.
  (* 三个都可以 *)
Proof.
    (* only des *)
    intros [].
        - simpl. reflexivity.
        - simpl. reflexivity. 
Qed.
Theorem zero_neqb_S'' : forall n:nat,
  0 =? (S n) = false.
  (* 三个都可以 *)
Proof.
    (* only induc *)
    intros n.
    induction n as [| n' H].
        - simpl. reflexivity.
        - simpl. reflexivity. 
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
  (* only duction *)
Proof.
    (* duction *)
    intros [].
        - simpl. reflexivity.
        - simpl. reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
  (* three ways *)
Proof.
    intros n.
    simpl. reflexivity.
Qed.
Theorem S_neqb_0' : forall n:nat,
  (S n) =? 0 = false.
  (* three ways *)
Proof.
    intros [].
        - simpl. reflexivity.
        - simpl. reflexivity.
Qed.
Theorem S_neqb_0'' : forall n:nat,
  (S n) =? 0 = false.
  (* three ways *)
Proof.
    intros n.
    induction n as [| n'].
        - simpl. reflexivity.
        - simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
(* three ways *)
Proof.
    intros n.
    simpl. rewrite add_comm. simpl. reflexivity.
Qed.
Theorem mult_1_l' : forall n:nat, 1 * n = n.
(* three ways *)
Proof.
    intros [| n'].
        - simpl. reflexivity.
        - simpl. rewrite add_comm. simpl. reflexivity.
Qed.
Theorem mult_1_l'' : forall n:nat, 1 * n = n.
(* three ways *)
Proof.
    intros n.
    induction n as [|n' H].
        - simpl. reflexivity.
        - rewrite <- H. simpl. rewrite add_comm. simpl. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
  (* only dest *)
Proof.
    intros [] [].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
Qed.
  
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
  (* only induction *)
Proof.
    intros n m p .
    induction n as [| n'].
    {simpl. reflexivity. }
    {simpl. rewrite IHn'. rewrite add_assoc. reflexivity. }
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
    intros n m p .
    induction n as [| n'].
        - simpl. reflexivity.
        - simpl. rewrite IHn'. rewrite mult_plus_distr_r. reflexivity.
Qed. 
Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.  
    intros n m p.
    rewrite add_assoc. rewrite add_assoc. 
    replace (m + n) with (n + m) .
        - reflexivity.
        - rewrite add_comm. reflexivity.
Qed.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).
Fixpoint incr (m: bin) : bin :=
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

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
    intros b.
    induction b as [| b' Hb' | b'' Hb''].
        - simpl. reflexivity.
        - simpl. reflexivity.
        - simpl. rewrite Hb''. 
          rewrite add_0_r_firsttry. rewrite add_0_r_firsttry. simpl.
          rewrite add_comm. reflexivity.
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
    match n with
    | O => Z
    | S p => incr(nat_to_bin(p))
    end.
Compute nat_to_bin(5).
Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
    intros n.
    induction n as [| n'].
        - simpl. reflexivity.
        - simpl. rewrite bin_to_nat_pres_incr. rewrite IHn'. reflexivity.
Qed.

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
    intros n .
    induction n as [| n].
        - reflexivity.
        - rewrite IHn. reflexivity.
Qed.
Definition double_bin (b:bin) : bin := 
    match b with
    | Z => Z
    | _ => B0 (b)
    end.
Compute (double_bin (B0 (B1 Z))).
Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
    intros b .
    induction b as [| |].
        - simpl. reflexivity.
        - simpl. reflexivity.
        - simpl. reflexivity.
Qed. 
 
Print bin.
Fixpoint normalize (b:bin) : bin :=
    match b with 
    | Z => Z
    | B0 b' => double_bin (normalize b')
    | B1 b' => B1 (normalize b')
    end.
Example normalize_1 : normalize (B0 (B0 Z)) = Z.
Proof.
    simpl. reflexivity.
Qed.
Example normalize_2 : normalize (B1 (B0 (B0 Z))) = B1 Z.
Proof.
    simpl. reflexivity.
Qed.

Lemma B1_incr: forall (b: bin),
    B1 (incr b) = incr (incr (B1 b)).
Proof.
    intros  [| |].
        - simpl. reflexivity.
        - simpl. reflexivity.
        - simpl. reflexivity.
Qed. 
Lemma nat_twice_plus_one: forall (n:nat),
    nat_to_bin (n + n + 1) = B1 (nat_to_bin n).
Proof.
    intros n .
    induction n as [| ].
        - simpl. reflexivity.
        - simpl. rewrite B1_incr. rewrite <- IHn.
          rewrite add_comm. simpl. 
          replace (n + (S n)) with (n+n+1).
            + reflexivity.
            + rewrite <- add_assoc.
              replace (n + 1) with (S n).
              {reflexivity. }
              {rewrite add_comm. simpl. reflexivity. }  
Qed.
Lemma nat_twice_plus_one': forall (n:nat),
    nat_to_bin (n + n + 1) = B1 (nat_to_bin n).
    (* copy  *)
Proof.
    intros n .
    induction n as [| ].
        - simpl. reflexivity.
        - simpl. replace (n + S n) with (S(n + n)).
            + simpl. rewrite IHn. simpl. reflexivity.
            + rewrite plus_n_Sm. reflexivity. 
Qed.
Theorem normalize_incr: forall (b: bin),
  incr (normalize b) = normalize (incr b).
Proof.
Admitted.
Lemma L1: forall (n: nat),
    (nat_to_bin (n + n)) = (double_bin (nat_to_bin n)).
Proof.
    intros n .
    induction n as [| ].
        - simpl. reflexivity.
        - rewrite <- double_plus. rewrite double_incr. simpl.
          rewrite double_plus.  rewrite IHn. rewrite double_incr_bin. reflexivity.
Qed.
Lemma L2: forall (n: nat),
    incr (double_bin (nat_to_bin n)) = B1 (nat_to_bin n).
Proof.
    intros n .
    induction n as [| ].
        - simpl. reflexivity.
        - simpl. rewrite double_incr_bin. rewrite IHn. rewrite B1_incr.
          reflexivity.
Qed. 
Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
    intros b .
    induction b as [| |].
        - simpl. reflexivity.
        - simpl. rewrite add_0_r_firsttry.
          rewrite <- IHb. rewrite L1. reflexivity.
        - simpl. rewrite add_0_r_firsttry.
          rewrite <- IHb. rewrite <- L2. rewrite L1. reflexivity.
Qed.