Print LoadPath.

From Coq Require Import Nat .

Inductive natprod : Type :=
  | pair (n1 n2 : nat).
Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.
Compute (fst (pair 3 5)).
Notation "( x , y )" := (pair x y).
Compute (fst (3,5)).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O   , _    => O
    | _   , O    => n
    | S n', S m' => minus n' m'
    end.

Theorem surjective_pairing' : forall (n m : nat),
    (n,m) = (fst (n,m), snd (n,m)).
Proof. reflexivity. Qed.
Theorem surjective_pairing_stuck : forall (p : natprod),
    p = (fst p, snd p).
Proof.
    intros p. 
    destruct p as [n m]. simpl. reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
    intros p. 
    destruct p as [n m]. simpl. reflexivity.
Qed.
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
    intros p. 
    destruct p as [n m]. simpl. reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Check [1 ; 2].
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.
Fixpoint length (l:natlist) : nat :=
    match l with
    | nil => O
    | h :: t => S (length t)
    end.
Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.
Notation "x ++ y" := (app x y)
    (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
    match l with
    | nil => default
    | h :: t => h
    end.
Definition tl (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => t
    end.
Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist := 
    match l with
    | nil => nil
    | O :: t => nonzeros(t)
    | h :: t => h :: nonzeros(t)
    end.

Example test_nonzeros:
nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.
Compute odd 5.
Fixpoint oddmembers (l:natlist) : natlist:=
    match l with 
    | nil => nil
    | h :: t => if (odd h) then h :: oddmembers t
                else oddmembers t
    end.
Example test_oddmembers:
oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
    length (oddmembers l).
    
Example test_countoddmembers1:
countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers2:
countoddmembers [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers3:
countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1, l2 with 
    | nil, _ => l2
    | _ , nil=> l1
    | m:: n , s:: t=> m:: s:: (alternate n t)
    end.
Example test_alternate1:
alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate2:
alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.
Example test_alternate3:
alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.
Example test_alternate4:
alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.

Definition bag := natlist.
Fixpoint count (v : nat) (s : bag) : nat:=
    match s with
    | nil => O
    | h:: t => if h =? v then (S (count v  t))
                else (count v t)
    end.
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.
Definition sum : bag -> bag -> bag := app.
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := v :: s.
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint member (v : nat) (s : bag) : bool:=
    match s with
    | nil => false
    | h:: t => if v =? h then true
                else (member v t)
    end.
Example test_member1: member 1 [1;4;1] = true.
Proof. simpl. reflexivity. Qed.    
Example test_member2: member 2 [1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_one (v : nat) (s : bag) : bag :=
    match s with 
    | nil => nil
    | h :: t => if v =? h then t
                else (h:: (remove_one v t))
    end.
Example test_remove_one1:
count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one2:
count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one3:
count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_one4:
count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag:= 
    match s with 
    | nil => nil
    | h :: t => if v =? h then (remove_all v t)
                else (h:: (remove_all v t))
    end.
Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint included (s1 : bag) (s2 : bag) : bool:=
    match s1 with
    | nil => true
    | h:: t => if (member h s2 ) then (included t (remove_one h s2))
                else false
    end.
Example test_subset1: included [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.
Example test_subset2: included [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Theorem add_inc_count : forall (n: nat) (l : bag),
    length (add n l) = (length l ) + 1.
Proof.
    intros n l .
    induction l as [| h t H] .
        - simpl. reflexivity.
        - simpl. rewrite <- H. simpl. reflexivity.
Qed.

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
    pred (length l) = length (tl l).
Proof.
intros l. destruct l as [| n l'].
- (* l = nil *)
    reflexivity.
- (* l = cons n l' *)
    reflexivity. Qed.
Theorem app_assoc : forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
    intros l1 l2 l3 .
    induction l1 as [| h t H].
        - simpl. reflexivity.
        - simpl. rewrite H. reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
length (l1 ++ l2) = (length l1) + (length l2).
Proof.
    intros l1 l2.
    induction l1 as [|n l H].
        - simpl. reflexivity.
        - simpl. rewrite <- H. reflexivity.
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
Theorem rev_length_firsttry : forall l : natlist,
length (rev l) = length l.
Proof.
    intros l.
    induction l as [| n l H].
        - simpl. reflexivity.
        - simpl. rewrite app_length. rewrite <- H.  rewrite <- add_comm.
          simpl. reflexivity.
Qed.

Search rev.
Search (_ + _ = _ + _).

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
    intros l.
    induction l as [|l l' H].
        - simpl. reflexivity.
        - simpl. rewrite H. reflexivity.
Qed.
Search app.
Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
    intros l1 l2.
    induction l1 as [| n l1 H].
    - induction l2 as [|].
        + simpl. reflexivity.
        + simpl. rewrite app_nil_r. reflexivity.
    - induction l2 as [| m l2 Hl].
        + simpl. rewrite app_nil_r. reflexivity.
        + simpl.  rewrite H. rewrite app_assoc. simpl. reflexivity.
Qed.

Search rev.
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
    intros l.
    induction l as [| n l H].
    - simpl. reflexivity.
    - simpl. rewrite rev_app_distr. rewrite H. simpl. reflexivity.
Qed.


Search app.
Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
    intros l1 l2 l3 l4.
    rewrite app_assoc.
    rewrite app_assoc. 
    reflexivity.
Qed.

Search nonzeros.
Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
    intros l1 l2.
    induction l1 as [| n l1 H].
    - simpl. reflexivity.
    - destruct n eqn: Hn.
        + simpl. rewrite H. reflexivity.
        + simpl. rewrite H. reflexivity.
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool:=
  match l1, l2 with
  | nil, nil => true
  | nil, _ => false
  | _, nil => false
  | n::t1, m::t2 => andb (n =? m) (eqblist t1 t2)
  end.
Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
  Proof. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
  Proof. reflexivity. Qed.

Search eq.
Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof. 
    intros l.
    induction l as [| n l H].
    - reflexivity.
    - simpl. assert (Hn: (n =? n) = true).
        + induction n as [|].
        {simpl. reflexivity. }
        {simpl. rewrite IHn. reflexivity. }
        + rewrite Hn. simpl. rewrite H. reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
    intros s.
    simpl. reflexivity.
Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
    intros n .
    induction n as [| n H].
    - simpl. reflexivity.
    - simpl. rewrite H. reflexivity.
Qed.

Search leb.
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
    intros s .
    induction s as [|n t H].
    - simpl. reflexivity.
    - destruct n as [| n].
        + simpl. rewrite leb_n_Sn. reflexivity.
        + simpl. rewrite H. reflexivity.
Qed.

Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
    intros f H n1 n2 Hn.
    rewrite  H.
    rewrite <- Hn.
    rewrite <- H.
    reflexivity.
Qed.
Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
    intros l1 l2 H.
    rewrite <- rev_involutive.
    rewrite <- H.
    rewrite rev_involutive.
    reflexivity.
Qed.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.
Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
    match l with
    | [] => None
    | x :: l' => match n with
                    | O => Some x
                    | S n' => nth_error l' n'
                    end
    end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Definition option_elim (def : nat) (o : natoption) : nat :=
    match o with
    | None => def
    | Some x => x
    end.
    
Definition hd_error (l : natlist) : natoption :=
    match l with
    | [] => None
    | n::t => Some n
    end.
Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
    hd default l = option_elim default (hd_error l).
Proof.
    intros l t.
    destruct l  as [| n l].
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (i j: id) :=
  match i, j with
  | Id x, Id y => x=? y
  end.

Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
    (* intros x. *)
    intros [x].
    simpl.
    induction x as [| x H].
    - simpl. reflexivity.
    - simpl. rewrite H. reflexivity.
Qed.
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).
Definition update (d:partial_map) (x:id) (val:nat) :=
  record x val d.

Fixpoint find (x:id) (d:partial_map) : natoption :=
  match d with
  | empty => None
  | record k v d' => if beq_id x k then Some v
                                    else find x d'
  end.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
    intros d x v .
    destruct d as [|i n d].
    - simpl. rewrite <- beq_id_refl. reflexivity.
    - simpl. rewrite <- beq_id_refl. reflexivity. 
Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    beq_id x y = false -> find x (update d y o) = find x d.
Proof.
    intros d x y o H.
    simpl. rewrite H. reflexivity.
Qed.
Inductive baz : Type :=
  | B
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).
Check 1.
Check Baz1 (Baz2 (Baz1 B) true).