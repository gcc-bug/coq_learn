From Coq Require Import Nat .

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check nil.
Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint repeat (X: Type)(x: X)(count: nat): list X:=
  match count with
  | 0 => nil X
  | S n => cons X x (repeat X x n)
  end.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Module MumbleGrumble.
Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.
Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

Fail Check d (b a 5).
Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
Fail Check e bool (b c 0).
End MumbleGrumble.
(* right
wrong
wrong
right
right
wrong*)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat' _ x count')
  end.
Definition list123 :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.
Definition list123' :=
  cons 1 (cons  2 (cons 3 (nil ))).

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.
Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil .
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l.
  induction l as [| x l H].
  - simpl. reflexivity.
  - simpl. rewrite H. reflexivity.
Qed. 
Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros X.
  intros l m n.
  induction l as [| x l H].
  - simpl. reflexivity.
  - simpl. rewrite H. reflexivity.
Qed.
Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X.
  intros l1 l2.
  induction l1 as [| n l1 H].
  - simpl. reflexivity.
  - simpl. rewrite H. reflexivity.
Qed.
Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X.
  intros l1 l2.
  induction l1 as [| n l1 H].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite H. rewrite app_assoc. reflexivity.
Qed.
Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X.
  intros l.
  induction l as [| n l H].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. rewrite H. simpl. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Arguments pair {X} {Y}.
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
  : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.
Compute (combine [1;2] [false;false;true;true]).

Fixpoint split {X Y : Type} (l : list (X*Y)) : 
(list X) * (list Y):=
  match l with
  | [] => ([],[])
  | (x,y)::t => (x:: fst(split(t)), y:: snd(split(t)))
  end. 
Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. simpl. reflexivity. Qed.

  Inductive option (X: Type) : Type :=
  | None : option X
  | Some : X -> option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
         : option X :=
  match n, l with
  | _, [] => None
  | O, x :: _ => Some x
  | S n', _ :: l' => nth_error l' n'
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | h :: _ => Some h
  end.


Check @hd_error.
Check hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.


Definition doit3times {X:Type} (f:X -> X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.

Definition minusTwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.
Example test_doit3times: doit3times minusTwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Fixpoint filter {X:Type} (test: X -> bool) (l:list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.

Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.
Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Compute 5 <=? 4.
Definition filter_even_gt7 (l : list nat) : list nat:=
  filter (fun n => andb (even n) (7<?n)) l.
  
Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. simpl. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. simpl. reflexivity. Qed.

Definition partition {X : Type}
  (test : X -> bool) (l : list X): list X * list X:=
  (filter test l, filter (fun n=> negb (test n)) l).

Compute partition odd [1;2;3;4;5].

Example test_partition1: partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.
Fixpoint map {X Y:Type} (f:X -> Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2:
  map odd [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example test_map3:
    map (fun n => [even n;odd n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Lemma map_l: forall(X Y:Type)(f:X->Y)(l1 l2:list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y.
  intros f.
  intros l1 l2.
  induction l1 as [| n t H].
  - simpl. reflexivity.
  - simpl. rewrite H. reflexivity.
Qed.
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y.
  intros f.
  intros l.
  induction l as [|n l H].
  - simpl. reflexivity.
  - simpl. rewrite <- H. rewrite map_l. simpl. reflexivity.
Qed.
Fixpoint flat_map {X Y: Type} 
  (f: X -> list Y) (l: list X): list Y :=
  match l with
  | [] => []
  | x::t => (f x)++(flat_map f t)
  end.
Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.
Fixpoint fold {X Y:Type} (f:X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)
  end.

Compute (fold plus [1;2;3;4] 0).
Check (fold andb).

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Compute (fold app [[1];[];[2;3];[4]] []).

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

Definition constfun {X:Type} (x:X) : nat -> X :=
  fun (k:nat)  => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.


Check plus.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.
Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X.
  intros l.
  induction l as [|n l H].
  - unfold fold_length. simpl. reflexivity.
  - simpl. assert (Hn: fold_length (n :: l)= S(fold_length (l))).
    + destruct l as [| m t ].
      {unfold fold_length. simpl. reflexivity. }
      {unfold fold_length. simpl. reflexivity. }
    + rewrite Hn. rewrite H. reflexivity.
Qed.

Theorem fold_length_correct' : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X.
  intros l.
  induction l as [|n l H].
  - unfold fold_length. simpl. reflexivity.
  - simpl. rewrite <- H. 
    unfold fold_length. simpl.
    reflexivity.
Qed.

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x t => ((f x):: t)) l [].
  
Compute fold_map plus3 [1;2;3].
Theorem fold_map_correct : forall X Y (f: X -> Y)(l : list X) ,
  fold_map f l = map f l.
Proof.
  intros X Y.
  intros f.
  intros l.
  induction l as [| x t H].
  - unfold fold_map. simpl. reflexivity.
  - simpl. rewrite <- H. unfold fold_map. simpl. reflexivity.
Qed.

Definition prod_curry {X Y Z : Type} (f: X * Y -> Z) : X -> Y -> Z :=
  fun x y => f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  (f (fst p) (snd p)).

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z .
  intros f.
  intros x y.
  unfold prod_curry.
  unfold prod_uncurry.
  simpl.
  reflexivity.
Qed.
  
Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z.
  intros f.
  intros [].
  unfold prod_curry.
  unfold prod_uncurry.
  simpl.
  reflexivity.
Qed.  

Fixpoint nth_error' {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if n =? O then Some a else nth_error' l' (pred n)
     end.

Search length.
Lemma list_n: forall (X:Type)(l: list X)(x: X),
  length (x:: l) = S(length l).
Proof.
  intros X.
  intros l x .
  destruct l as [| y t].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
Lemma nth_len: forall (X:Type)(l: list X),
  nth_error' l (length l) = None .
Proof.
  intros X.
  intros l.
  induction l as [| x t H].
  - simpl. reflexivity.
  - simpl. rewrite H. reflexivity.
Qed.

Theorem nth_length: forall (X: Type)(l : list X)(n: nat),
  length l = n -> nth_error' l n = None.
Proof.
  intros X.
  intros l n.
  intros H.
  rewrite <- H.
  rewrite nth_len.
  reflexivity.
Qed.
Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition three : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f(f (f x)).

Print zero.

Example zero_church_peano : zero nat S O = 0.
Proof. reflexivity. Qed.
Example one_church_peano : one nat S O = 1.
Proof. reflexivity. Qed.
Example two_church_peano : two nat S O = 2.
Proof. reflexivity. Qed.

(* Compute . *)
Definition scc (n : cnat) : cnat:=
  fun (X: Type) (f: X->X) (x: X) => f (n X f x) . 

Compute scc zero nat S O.
Example scc_1 : scc zero = one.
Proof. reflexivity. Qed.
Example succ_2 : succ 1 = 2.
Proof. reflexivity. Qed.

Example succ_3 : succ 2 = 3.
Proof. reflexivity. Qed.

Definition plus (n m : cnat) : cnat:=
  fun (X: Type) (f: X->X) (x: X) => n X f ( m X f x).

Compute plus three one nat S O.

Definition mult (n m : cnat) : cnat:=
  fun (X: Type) (f: X->X) => n X (m X f).

Compute mult three zero nat S O.