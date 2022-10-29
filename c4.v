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
End MumbleGrumble.