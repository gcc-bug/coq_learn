From Coq Require Import Nat .
From Coq Require Import List.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]") : list_scope.
Check [5;4].


Theorem silly1 : forall (n m : nat),
    n = m -> n = m.
Proof.
  intros n m.
  intros H.
  apply H.
Qed.
(* Q : rewrite 与 apply的区别是什么？ *)
Theorem silly2 : forall (n m o p : nat),
n = m ->
(n = m -> [n;o] = [m;p]) ->
[n;o] = [m;p].
Proof.
  intros n m o p.
  intros H1 H2.
  apply H2.
  apply H1.
Qed.
Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

(* ans: see following example where rewrite static doesn't work *)
(* ans: rewrite only replace but apply can recongnize forall *)

Theorem silly2a' : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  (* rewrite eq2. *)
  Admitted.

Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
  intros p.
  intros H1 H2 H3.
  apply H2. apply H1. apply H3.
Qed.

(* ans: apply can't match for follwing proof. but rewrite can *)
Theorem silly3 : forall (n m : nat),
    n = m -> m = n.
Proof.
  intros n m.
  intros H.
  Fail apply H.
  symmetry. apply H.
Qed.

Search rev (rev _).
Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l s.
  intros H.
  rewrite H. symmetry. apply rev_involutive.
Qed.
(* ans: apply is more likely to reflexivity and rewrite *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f.
  intros H0 H1.
  rewrite H0. apply H1.
Qed.

Theorem trans_eq : forall (X: Type) (n m o: X),
  n = m -> m = o -> n = o.
Proof.
  intros X.
  intros b m o.
  intros H0 H1.
  rewrite H0. apply H1.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f .
  intros H0 H1.
  (* apply trans_eq with (m:=[c;d]). *)
  (* apply trans_eq with [c;d]. *)
  transitivity [c;d].
  apply H0. apply H1.
Qed.
Fixpoint minustwo (n:nat): nat:=
  match n with
  | O => O
  | S O => O
  | S(S m) => minustwo m
  end.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p.
  intros H0 H1.
  transitivity m.
  apply H1. apply H0.
Qed.
(* Search S. *)
Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m .
  intros H0.
  assert (H1: n = pred(S n)).
  reflexivity. rewrite H1. rewrite H0. simpl. reflexivity.
Qed. 

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m .
  intros H.
  injection H as H. apply H.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o.
  intros H.
  injection H as H0 H1. transitivity o. 
  apply H0.  symmetry. apply H1.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X.
  intros x y z l j.
  intros H0 H1.
  injection H0 as H00 H01.
  assert (H: y :: l =  z :: l).
  {transitivity j. apply H01. apply H1. }
  {injection H as H. transitivity z. apply H00. symmetry. apply H. }
Qed.

Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra. discriminate contra. Qed.
Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X.
  intros x y z l.
  intros H0 H1.
  discriminate H1.
Qed.

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
  intros H.
  destruct n as [| n].
  - reflexivity.
  - discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.
Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. f_equal. apply H. Qed.
(* Q: the difference between f_equal with injection *)

Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b ->
  (n =? m) = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.
(* simpl in H *)

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q.
  intros H0 H1.
  (* symmetry. apply H0. symmetry. apply H1. *)
  symmetry in H1. apply H0 in H1. symmetry in H1. apply H1.
Qed.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [| n Hn].
  - intros m . intros H. 
    destruct m as [| m].
    {reflexivity. } {discriminate H. }
  - intros m . intros H. 
    destruct m as [| m].
    {discriminate H. }
    {apply Hn in H. apply eq_implies_succ_equal. apply H. }
Qed.

Print plus_n_Sm.
Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n. 
  induction n as [| n Hn].
  - intros [| m].
    + reflexivity.
    + simpl. intros H. discriminate H.
  - intros [| m].
    + simpl. intros H. discriminate H.
    + simpl. intros H. injection H as H.
      rewrite <- plus_n_Sm in H. rewrite <- plus_n_Sm in H.
      injection H as H. apply Hn in H.
      apply eq_implies_succ_equal. apply H.
Qed.
Search double nat.
Print double.
(* Print double_S. *)
Lemma double_S: forall n:nat,
  double (S n )= S(S(double n)) .
Proof.
  intros [| n].
  - simpl. reflexivity.
  - unfold double. simpl. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. rewrite double_S in eq. rewrite double_S in eq.
      injection eq as goal. apply goal. Qed.

Lemma nth_error_x:forall(X:Type)(n: nat)(l: list X)(x: X),
  nth_error (x::l) (S n) = nth_error l n .
Proof.
  intros. simpl. reflexivity. 
Qed.
      
Theorem nth_error_after_last: forall (X : Type)(n : nat)  (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros X.
  intros n l.
  generalize dependent n.
  induction l as [| x t IH].
  - simpl. intros n H. rewrite <- H. reflexivity.
  - intros n H. destruct n as [| n].
    + discriminate H. 
    + rewrite nth_error_x. apply IH.
      simpl in H. injection H as H. apply H.
Qed. 

Definition square n := n * n.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
Admitted.
Theorem  mult_comm:forall n m :nat,
 n* m = m*n .
Proof.
Admitted.
Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros.
  unfold square.
  rewrite -> mult_assoc.
  assert (H : n * m * n = n * n * m).
  - rewrite -> mult_comm. apply mult_assoc.
  - rewrite -> H. rewrite -> mult_assoc.
    reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  (* unfold bar. *)
  (* simpl. *)
  destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros.
  unfold sillyfun.
  destruct ( n =? 3).
  - reflexivity.
  - destruct (n =? 5).
    + reflexivity.
    + reflexivity.
Qed.

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.



Lemma nail: forall (X: Type)(x:X)(l1 l2: list X),
  l1 = l2 -> x::l1 = x::l2.
Proof.
  intros X.
  intros x l1 l2.
  intros H.
  simpl. rewrite H. reflexivity.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y.
  intros l.
  induction l as [| (x,y) t Ht].
  - intros l1 l2 H. injection H as H0 H1.
    rewrite <- H0. rewrite <- H1. simpl. reflexivity.
  - intros l1 l2 H. 
    (* unfold split in H. *)
    (* Q: why unfold make the H more compleable than simpl? *)
    simpl in H. destruct (split t) as [t1 t2].
    injection H as H0 H1. rewrite <- H0. rewrite <- H1.
    simpl. apply nail. apply Ht. reflexivity.
    (* ansL inversion =  injection in context and rewrite in goal used context*)
    (* destruct l1 as [|x1 l1].
    + injection H as H0 H1. discriminate H0.
    + destruct l2 as [| y2 l2].
      {injection H as H0 H1 H2. discriminate H2. }
      {simpl. injection H as H0 H1 H2 H3. rewrite H0.
       rewrite H2. apply nail. apply Ht.
       rewrite H1. rewrite H3. reflexivity.  } *)
Qed.

Theorem combine_split' : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| h t IH].
  - intros.
    inversion H.
    reflexivity.
  - intros.
    inversion H.
    destruct h.
    destruct (split t).
    simpl in H1.
    inversion H1.
    simpl.
    apply nail.
    apply IH.
    reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if eqb n 3 then true
  else if eqb n 5 then true
  else false.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     odd n = true.
Proof.
  intros.
  unfold sillyfun1 in H.
  destruct (eqb n 3) eqn:neq3.
  - apply eqb_true in neq3.
    rewrite -> neq3.
    reflexivity.
  - destruct (eqb n 5) eqn:neq5.
    + apply eqb_true in neq5.
      rewrite -> neq5.
      reflexivity.
    + discriminate H.
    (* + inversion H. *)
    (* ans: inversion also discriminate H*)
Qed.

Theorem sillyfun1_odd' : forall (n : nat),
     sillyfun1 n = true ->
     odd n = true.
Proof.
  intros.
  unfold sillyfun1 in H.
  destruct (eqb n 3).
  - Abort.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct (f true) as [|] eqn: ft.
  - destruct b.
   + rewrite ft. rewrite ft. apply ft.
   + destruct (f false) as [|] eqn: ff.
     {rewrite ft. apply ft. }
     {rewrite ff. apply ff. }
  - destruct b.
   + destruct (f false) as [|] eqn: ff.
     {rewrite ft. rewrite ff. apply ft. }
     {rewrite ft. rewrite ff. apply ff. }    
   + destruct (f false) as [|] eqn: ff.
     {rewrite ft. apply ff. }
     {rewrite ff. apply ff. }
Qed.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n.
  induction n as [| n Hn].
  - intros [|m].
    + simpl. reflexivity.
    + simpl. reflexivity.
  - intros [|m].
    + simpl. reflexivity.
    + simpl. apply Hn.
Qed.

Lemma eqb_true_: forall (n m : nat),
  n = m -> ((n =? m) = true).
Proof.
  intros n.
  induction n as [|n Hn].
  - intros m H. rewrite <- H. simpl. reflexivity.
  - intros m H. induction m as [| m Hm].
    + discriminate H.
    + simpl. apply Hn. injection H as H. apply H.  
Qed.
Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p.
  intros H0 H1. 
  apply eqb_true_.
  apply eqb_true in H0. apply eqb_true in H1.
  (* ans: there is a different between apply in context with it in goal *)
  transitivity m. apply H0. apply H1.
Qed.

Definition split_combine_statement : Prop :=
  forall (X Y: Type) (l1 :list X)(l2 :list Y),
  length l1 = length l2 ->
  split (combine l1 l2) = (l1, l2).
Theorem split_combine : split_combine_statement.
Proof.
  intros X Y.
  intros l1.
  induction l1 as [| x t1 Hx].
  - intros l2 H. simpl.
    destruct l2 as [| y t2].
    + reflexivity.
    + simpl in H. discriminate H.
  - intros l2 H. 
    destruct l2 as [| y t2].
    + discriminate H.
    + simpl in H. injection H as H.
      apply Hx in H. simpl. rewrite H.
      reflexivity.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X.
  intros test x l t.
  generalize dependent x.  generalize dependent t.
  induction l as [| n l Hl].
  - simpl. intros t x H. discriminate H.
  - simpl. destruct (test n) eqn: E.
    + intros t x H. injection H as H0 H1.
      rewrite H0 in E. apply E.
    + intros t x H. apply Hl in H. apply H.
Qed.

Compute andb true false.
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X)
  : bool := 
  match l with 
  | [] => true
  | x:: t => if test x then forallb test t
             else false
  end.

Example forallb_1: forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.

Example forallb_2: forallb negb [false;false] = true.
Proof. reflexivity. Qed.

Example forallb_3: forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.

Example forallb_4: forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) :
  bool:=
  match l with
  | [] => false
  | x::t => if test x then true
            else existsb test t
  end.

Example existsb_1: existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.

Example existsb_2: existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.

Example existsb_3: existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.

Example existsb_4: existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) :
  bool:= negb (forallb (fun x => negb(test x)) l). 
Example existsb_1': existsb' (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.

Example existsb_2': existsb' (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.

Example existsb_3': existsb' odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.

Example existsb_4': existsb' even [] = false.
Proof. reflexivity. Qed.

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros X.
  intros test l.
  induction l as [| x t H].
  - simpl. unfold existsb'. simpl. reflexivity.
  - unfold existsb'. simpl.
    destruct (test x).
    + simpl. reflexivity.
    + simpl. rewrite H. unfold existsb'. reflexivity.
Qed.