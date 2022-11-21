From Coq Require Import Nat .
From Coq Require Import List.
Check (3 = 3).
Check forall n m : nat, n + m = m + n.

Check forall n : nat, n = 2.
Check 3 = 5.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_injective: injective S.
Proof.
  intros n m H. injection H as H . apply H.
Qed.

Check @eq.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  {simpl. reflexivity. }
  {simpl. reflexivity. }
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros a b.
  intros A B.
  split. apply A. apply B.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  reflexivity. reflexivity.
Qed.

Search plus.
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m.
  intros H. apply and_intro.
  - destruct n as [|].
    {reflexivity. }{discriminate H. }
  - destruct m as [|].
    {reflexivity. }{rewrite <- plus_n_Sm in H. discriminate H. }
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m.
  intros [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m.
  intros H.
  apply and_exercise in H.
  destruct H as [Hn Hm].
  rewrite Hn. simpl. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q.
  intros [Hp _].
  apply Hp.
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros p q.
  intros [_ H].
  apply H.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros p q.
  intros H.
  split.
  - apply proj2 in H. apply H.
  - apply proj1 in H. apply H.
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split. apply HP. apply HQ.
  - apply HR.
Qed.

Search mult.
Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m.
  intros [Hn | Hm].
  - rewrite Hn. simpl. reflexivity.
  - rewrite Hm. rewrite <- mult_n_O. reflexivity.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B.
  intros H.
  left.
  apply H.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [| n].
  - left. reflexivity.
  - right. simpl. reflexivity.
Qed.

Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m.
  intros H.
  destruct n as [| n].
  - left. reflexivity.
  - right. destruct m as [| m].
    + reflexivity.
    + discriminate H.
Qed.

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros p q.
  intros [H | H].
  - right. apply H.
  - left. apply H.
Qed.


Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

End MyNot.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros p H.
  destruct H.
Qed.

Fact not_implies_our_not : forall (P:Prop),
  ~P -> (forall (Q:Prop), P -> Q).
Proof.
  intros p.
  intros H.
  intros q.
  intros Hp.
  destruct H.
  apply Hp.
Qed.

Notation "x <> y" := (~(x = y)).
Check (0 <> 1).

Theorem zero_not_one : ~(0 = 1).
Proof.
  unfold not.
  intros H. discriminate H.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.
Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed.
Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H. Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros p q.
  intros H.
  unfold not. intros hq hp.
  apply H in hp. apply hq in hp. destruct hp.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  unfold not.
  intros p. intros [hp hq].
  apply hq in hp. destruct hp.
Qed.

Search False.
Theorem de_morgan_not_or : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not.
  intros p q. intros H.
  split.
  - intros h. assert (Hp: p-> p\/ q).
    {apply or_intro. } 
    {apply Hp in h. apply H in h. destruct h. }
  - intros h. assert (Hp: q-> q\/ p).
    {apply or_intro. } 
    {apply Hp in h. apply or_commut in h. apply H in h. destruct h. }
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  unfold not.
  intros b.
  intros H.
  destruct b as [].
  - apply ex_falso_quodlibet. apply H.
    reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_fals' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - exfalso. apply H. reflexivity.
  - reflexivity.
Qed.

Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.
Theorem disc_example : forall n, ~ (O = S n).
Proof.
  intros n.
  unfold not. intros H.
  assert (h: disc_fn 0).
  - simpl. apply I.
  - rewrite H in h. simpl in h. apply h.
Qed.

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros p q.
  unfold iff. intros [H0 H1].
  split.
  apply H1. apply H0.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b.
  split.
  - intros H. apply not_true_is_false. apply H.
  - intros H h. rewrite H in h. discriminate h.
Qed.

Theorem apply_iff_example1 : forall P Q R : Prop,
  (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros p q r. intros Hpq Hqr Hp.
  apply Hqr. apply Hpq. apply Hp.
Qed.

Theorem apply_iff_example2 : forall P Q R : Prop,
  (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros p q r. intros Hpq Hpr Hq.
  apply Hpr. apply Hpq. apply Hq.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros p q r.
  split.
  - intros H. split.
    + destruct H as [].
      {left. apply H. }
      {right. apply proj1 in H. apply H. }
    + destruct H as [].
      {left. apply H. }
      {right. apply proj2 in H. apply H. }
  - intros [[H0 | H1] [H2 | H3]].
    + left. apply H0.
    + left. apply H0.
    + left. apply H2.
    + right. split.
      {apply H1. }
      {apply H3. }
Qed.   

From Coq Require Import Setoids.Setoid.

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros p q r.
  split.
  - intros [Hp |[ Hq| Hr]].
    +  left. left. apply Hp.
    +  left. right. apply Hq.
    +  right. apply Hr.
  - intros [[Hp| Hq]| Hr].
    +  left. apply Hp.
    +  right. left. apply Hq.
    +  right. right. apply Hr.
Qed.

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p. 
  rewrite mul_eq_0.
  rewrite mul_eq_0.
  rewrite  or_assoc.
  reflexivity.
Qed.

Definition Even x := exists n : nat, x = double n.
Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  rewrite Hm.
  reflexivity.
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X. intros P H.
  unfold not. intros [x E].
  apply E in H. apply H.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X.
  intros P Q .
  unfold iff. split.
  - intros [x H]. destruct H as [].
    + left. exists x. apply H.
    + right. exists x. apply H.
  -intros [H|H].
    + destruct H as [x H]. exists x. left. apply H.
    + destruct H as [x H]. exists x. right. apply H.
Qed. 
Search S.   
Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n+x.
Proof.
  intros n.
  induction n as [| n Hn].
  - intros m. intros H. 
    destruct m as [| m].
    + exists 0. simpl. reflexivity.
    + exists (S m). simpl. reflexivity.
  - intros m. intros H.
    destruct m as [| m].
    + simpl in H. discriminate H.
    + simpl in H. apply Hn in H.
      destruct H as [x0 H]. exists x0.
      simpl. apply eq_S.
      apply H.
Qed.

Theorem plus_exists_leb : forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof.
  intros n.
  induction n as [| n Hn].
  - intros m. intros H. simpl. reflexivity.
  - intros m. intros [x0 H].
    destruct m as [| m].
    + discriminate H.
    + simpl. apply Hn. exists x0.
      simpl in H. apply eq_add_S. apply H.
Qed.

Notation "[ ]" := nil .
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: t => x = x' \/ In x t
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* unfold In. *)
  right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  intros n. intros [H | [H |H]].
  - exists 1. rewrite H. reflexivity.
  - exists 2. rewrite H. reflexivity.
  - simpl in H. exfalso. apply H.
Qed.


Example In_example_2' :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n. intros [H | [H | []]].
  - exists 1. rewrite H. reflexivity.
  - exists 2. rewrite H. reflexivity.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l -> In (f x) (map f l).
Proof.
  intros A B.
  intros f l. induction l as [|s l Hl].
  (* - intros x. intros H. simpl in H. exfalso. apply H. *)
  (* or: *)
  - intros x. intros [].
  - intros x. intros [Hx | H].
    + simpl. left. rewrite Hx. reflexivity.
    + simpl. right. apply Hl. apply H.  
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B.
  intros f l y.
  split.
  - induction l as [|a t Ht].
    + intros [].
    + intros [Ha | H].
      * exists a. split. 
        {symmetry. apply Ha. }
        {simpl. left. reflexivity. }
      * apply Ht in H. destruct H as [x0 [Hx H]].
        exists x0. split.
        {apply Hx. }
        {simpl. right. apply H. }
  - induction  l as [|a t Ht].
    + intros [x0 [Hx []]].
    + intros [x0 [Hx H]].
      simpl. destruct H as [Ha| H].
      * left. symmetry. 
        rewrite <- Ha. apply Hx.
      * right. apply Ht. 
        exists x0. split. 
        {apply Hx. }
        {apply H. }
Qed.
(* Q:如何判断是否需要generalise 变量 *)

Lemma in_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A .
  intros l1 l2 a.
  split.
  - induction l1 as [| s1 t1 Ht].
    + simpl. intros H. right. apply H.
    + simpl. intros [Hs | H].
      * left. left. apply Hs.
      * apply Ht in H. apply or_assoc.
        right. apply H.
  - induction l1 as [| s1 t1 Ht].
    + simpl. intros [[]| H]. apply H.
    + simpl. intros H. apply or_assoc in H.
      destruct H as [Hs | H].
      * left. apply Hs.
      * right. apply Ht in H. apply H.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) :
  Prop :=
    match l with
    | [] => True
    | t::s => (P t) /\ (All P s)
    end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T.
  intros P l.
  split.
  - induction l as [| t s Hs].
    + simpl. intros H. reflexivity.
    + simpl. intros H. split.
      * apply H. left. reflexivity.
      * apply Hs. intros x. intros Hxs.
        apply H. right. apply Hxs.
  - induction l as [| t s Hs].
    + intros []. intros x. intros [].
    + intros [Hpt Hps]. intros x. 
      intros [Hxt | Hxs].
      * rewrite Hxt. apply Hpt.
      * apply Hs.
        {apply Hps. }
        {apply Hxs. }
Qed.
Compute odd 3.
Definition combine_odd_even (Podd Peven : nat -> Prop)(n:nat) : 
Prop:= if odd n then Podd n
       else Peven n.
                             
Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true ->  Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros O E n. intros Ht Hf.
  unfold combine_odd_even.
  destruct (odd n).
  - apply Ht. reflexivity.
  - apply Hf. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros O E n. intros Hc Ho.
  unfold combine_odd_even in Hc.
  rewrite Ho in Hc. apply Hc.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = false ->
    Peven n.
Proof.
  intros O E n. intros Hc Ho.
  unfold combine_odd_even in Hc.
  rewrite Ho in Hc. apply Hc.
Qed.

Check PeanoNat.Nat.add_comm.
Lemma plus_comm3 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite -> PeanoNat.Nat.add_comm.
  rewrite -> (PeanoNat.Nat.add_comm p m).
  reflexivity.
Qed.

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A.
  intros a l. intros H.
  unfold not. intros E.
  rewrite E in H. simpl in H. apply H.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.


(** Use [apply ... in ...] *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(** Explicitly apply the lemma to the value for [x]. *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(** Explicitly apply the lemma to a hypothesis. *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Search mult 0.
Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n l. intros H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  (* Q: 各个含义是什么 *)
  rewrite PeanoNat.Nat.mul_0_r in Hm. rewrite <- Hm. reflexivity.
  Qed.

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. simpl. reflexivity. Qed.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. reflexivity. Qed.

Search add.
Lemma even_double : forall k, even (double k) = true.
Proof.
  intros n. unfold double. induction n as [|n H].
  - simpl. reflexivity.
  - simpl. rewrite <- plus_n_Sm. apply H.   
Qed.

Search negb.
(** **** Exercise: 3 stars, standard (even_double_conv) *)
Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
    intros n.
    induction n as [| n' H].
    {simpl. reflexivity. }
    {rewrite H. simpl. rewrite Bool.negb_involutive. reflexivity. }
Qed.
Search double.
Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  intros n.
  induction n as [| n [x H]].
  - exists 0. reflexivity.
  - destruct (even n) eqn :E.
    + apply Bool.negb_false_iff in E.
      rewrite <- even_S in E.
      rewrite E. exists x. rewrite H. reflexivity.
    + apply Bool.negb_true_iff in E.
      rewrite <- even_S in E.
      rewrite E. exists (S x). rewrite H. simpl. 
      rewrite PeanoNat.Nat.double_S.
      reflexivity.
Qed.
  
Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
  (* Q: How to use destruct在其他引入命题中 *)
    rewrite H in Hk. exists k. apply Hk.
  - intros [k H]. rewrite H. apply even_double.
Qed.

Search andb.
Theorem andb_true_iff : forall b1 b2:bool,
   andb b1 b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H. split.
    + destruct b1 eqn:E.
      {reflexivity. }
      {simpl in H. discriminate H. }
    + destruct b2 eqn:E. 
      {reflexivity. }
      {rewrite Bool.andb_false_r in H. discriminate H. }
  - intros [B1 B2]. rewrite B1. rewrite B2.
    simpl. reflexivity.
Qed.   
Search orb.
Theorem orb_true_iff : forall b1 b2,
  orb  b1  b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H. destruct b1 as [|].
    + left. reflexivity.
    + right. destruct b2 as [|].
      {reflexivity. }
      {simpl in H. discriminate H. }
  - intros [B1 | B2].
    + rewrite B1. simpl. reflexivity.
    + rewrite B2. rewrite Bool.orb_true_r. reflexivity.
Qed.   

Search eqb.
Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y. split.
  - intros H E. rewrite E in H.
    simpl in H. rewrite (PeanoNat.Nat.eqb_refl y) in H.
    discriminate H.
  - unfold not. intros H. 
    destruct (x =? y) as [|] eqn: E.
    + apply PeanoNat.Nat.eqb_eq in E. apply H in E.
      exfalso. apply E.
    + reflexivity.
Qed. 

Theorem eqb_neq' : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y.
  rewrite <- (not_true_iff_false (x =? y)).
  unfold not. split.
  - intros H E. rewrite E in H.
    rewrite (PeanoNat.Nat.eqb_refl y) in H.
    destruct H as []. reflexivity.
  - intros H E. apply H.
    apply PeanoNat.Nat.eqb_eq. apply E.
Qed. 

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool:=
  match l1,l2 with
  | [],[] => true
  | [], _ => false
  | _ ,[] => false
  | n1::t1,n2::t2 => andb (eqb n1 n2) (eqb_list eqb t1 t2)
  end.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A.
  intros E IH. intros l1 l2.
  split.
  - generalize dependent l2. 
    induction l1 as [|a1 l1 Hl].
    + intros l2. intros H.
      destruct l2 as [| a2 l2].
      {reflexivity. }
      {simpl in H. discriminate H. }
    + intros l2. intros H.
      destruct l2 as [| a2 l2].
      {simpl in H. discriminate H. }
      { simpl in H. apply andb_true_iff in H.
        destruct H as [H1 H2].
        apply IH in H1. apply Hl in H2.
        rewrite H1. rewrite H2.
        reflexivity. }
  - generalize dependent l2.
    induction l1 as [|a1 l1 Hl].
    + intros l2. intros H.
      rewrite <- H. simpl.
      reflexivity.
    + intros l2. intros H.
      destruct l2 as [| a2 l2].
      { rewrite H. simpl. 
        reflexivity. }
      { injection H as H1 H2.
        apply IH in H1. apply Hl in H2.
        simpl. rewrite H1. rewrite H2.
        reflexivity.  
      }   
Qed.
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X)
  : bool:=
  match l with
  | [] => true
  | h::t => if test h then forallb test t
            else false
  end.
Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X.
  intros T l. split.
  - induction l as [|h l IH].
    + simpl. reflexivity. 
    + simpl. intros H. destruct (T h).
      * split. 
        {reflexivity. }
        {apply IH. apply H. }
      * discriminate H.
  - induction l as [|h l IH].
    + simpl. reflexivity.
    + intros [H1 H2].
      apply IH in H2. unfold forallb.
      destruct (T h).
      * apply H2.
      * discriminate H1.
Qed. 

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P. intros [|] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply PeanoNat.Nat.eqb_eq.
Qed.

Theorem excluded_middle_irrefutable: forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros P.
  unfold not. intros H. apply H.
  right.  intros E. apply H.
  left. apply E.
Qed.
Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle.
  intros IH X P E x.
  assert (H: P x \/ ~ P x).
  - apply IH.
  - destruct H as [H|H].
    + apply H.
    + exfalso. apply E. exists x. apply H.
Qed.

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q). 