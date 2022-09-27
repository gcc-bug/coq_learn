(* Curry-Howard *)

Lemma vdash : nat -> nat.
Proof.
  intro x.
  exact (x + 3).
Defined.
Print vdash.

Lemma test_Defined : nat * nat.
Proof.
  exact (1, 2).
Defined.

Print test_Defined.
Compute (match test_Defined with (a, b) => b end).

Lemma test_Qed : nat * nat.
Proof.
  exact (1, 2).
Qed.

Print test_Qed.
Compute (match test_Qed with (a, b) => b end).

(* Function *)
Section Functions.

Check (fun x : nat => x + 1) : (nat -> nat).

Eval cbv beta in ((fun x => x + 1) 2).

Lemma beta_reduction : (fun x => x + 1) 2 = 3.
Proof.
  cbv beta.
  Admitted.

End Functions.


(* Product *)
Section Product.


Check (1 : nat, true).
Check (fst (1 : nat, true)).
Compute (snd (1 : nat, true)).

Definition prod_ex1 A B : A * B -> B * A := (fun p : A * B => (snd p, fst p)).

Print prod_ex1.

Lemma prod_ex1' A B : A * B -> B * A.
Proof.
  exact (fun p : A * B => (snd p, fst p)).
Defined.

Print prod_ex1'.


Lemma prod_ex1'' A B : A * B -> B * A.
Proof.
  intro p.
  destruct p as [a b].
  split.
  - exact b.
  - exact a.
Defined.

Print prod_ex1''.

End Product.

(* Coproduct *)
Section Coproduct.

Check (inl 1) : nat + bool.

Check (match (inl 1) : nat + bool with
       | inl n => n + 1
       | inr b => 0
      end).

Compute (match (inl 1) : nat + bool with
       | inl n => n + 1
       | inr b => 0
      end).

(* f := fun n : nat => n + 1 *)
(* g := fun b : bool => 0 : nat *)
(* f \oplus g is like *)
Definition coprod_oplus {A B C} (f : A -> C) (g : B -> C) :=
  fun p : A + B =>
    match p with
    | inl a => f a
    | inr b => g b
    end.

Compute coprod_oplus (fun n => n + 1) (fun b => 0) (inl 1).
Compute coprod_oplus (fun n => n + 1) (fun b => 0) (inr true).

End Coproduct.

(* False *)
Section False.

Print False.

Variable A : Prop.

Definition False_imp_A : False -> A :=
  fun f : False =>
    match f with end.

Locate "~".
Print not.

Check (not A).
Eval cbv delta in (not A).
Eval compute in (not A).

Definition A_imp_notnotA : A -> (~ ~ A):=
  fun (x : A) =>
  fun (f : A -> False) =>
    f x.

End False.

(* Law of Excluded Middle *)
Section LEM.

Definition true_not_false : ~ (true = false) :=
  fun (p : true = false) =>
    match p in eq _ x return (if x then True else False) with
    | eq_refl _  => I
    end.
(* Check https://coq.inria.fr/distrib/current/refman/language/core/inductive.html#destructors if you are interested *)

Print eq_ind.
Definition true_not_false' : ~ (true = false) :=
  fun (p : true = false) =>
    eq_ind true (fun x => if x then True else False) I false p.

Lemma true_not_false'' : ~ (true = false).
Proof.
  intro p.
  discriminate.
Defined.
Print true_not_false''.

Fixpoint is_even (n : nat) : bool :=
  match n with
  | O => true
  | S n => negb (is_even n)
  end.

Check eq_refl true.
Definition is_even_computable n : ((true = is_even n) + (~(true = is_even n))):=
  match (is_even n) with
  | true => inl (eq_refl true)
  | false => inr true_not_false
  end.

Compute is_even_computable 2.
Compute is_even_computable 3.

Hypothesis is_even_LEM : forall n, ((true = is_even n) + (~(true = is_even n))).

Compute is_even_LEM 2.


Variable A : Prop.


(* LEM and Proof By Contradiction *)

Definition LEM_PBC : (A + ~ A) -> (~ ~ A -> A) :=
  fun (LEM_A : A + ~A) => 
  fun (H : ~ ~ A) =>
  match LEM_A with 
  | inl x => x
  | inr x => False_imp_A A (H x)
  end.


Definition not_not_LEM : ((A + ~ A) -> False) -> False :=
  fun (p : (A + ~ A) -> False) =>
    let p1 := fun a => (p (inl a)) in
    let p2 := inr p1 in
    p p2.
    
Definition PBC_LEM : (forall P, ((P -> False) -> False) -> P) -> (A + ~A) :=
  fun (PBC : forall P, ((P -> False) -> False) -> P) =>
    PBC _ not_not_LEM.

End LEM.

(* Dependent function *)
Section Dep_Func.

Check (fun (x : nat) => eq_refl x) : forall (x : nat), x = x.
Compute (fun (x : nat) => eq_refl x) 2.

Check (fun (x : nat) => x + 1) : nat -> nat.
Check (fun (x : nat) => x + 1) : forall (x : nat), nat.

End Dep_Func.

(* Dependent pair *)
Section Dep_Pair.


(* ex *)
Print ex.
Check (exists (x : nat), x = 2).
Definition exeq2 : exists x, x = 2 := (ex_intro (fun x => x = 2) 2 (eq_refl 2)).
Fail Check (match exeq2 with ex_intro _ n _ => n end).

(* sigT *)
Print sigT.
Check ({x & x = 2}).
Definition sigTeq2 : {x & x = 2} := (existT (fun x => x = 2) 2 (eq_refl 2)).

Compute (match sigTeq2 with existT _ n _ => n end).
Fail Compute (match sigTeq2 with existT _ _ p => p end).
Compute (match sigTeq2 as x return (match x with existT _ n _ => n = 2 end) with existT _ _ p => p end).
Compute (projT2 sigTeq2).
Search _ sigT "proj".

(* induction principle *)
Locate "*".
Check prod_ind.
Variable A B : Type.

(* ind_{A * B} *)
Check @prod_rect A B.
Locate "+".
Definition my_fst A B z := @prod_rect A B (fun p => A) (fun x y => x) z.
Compute my_fst nat nat (2, 3).

Inductive My_Ind_Type : Set :=
  | Case1 : My_Ind_Type
  | Case2 : My_Ind_Type
  | Case3 : My_Ind_Type.

Check My_Ind_Type_ind.

Check sum_ind.

End Dep_Pair.

(* Nat *)
Section Nat.

Check nat_ind.
Print Nat.add.

End Nat.

(* Eq *)
Section Eq.

Compute ((fun x => x + 1) 2).
Eval cbv beta in ((fun x => x + 1) 2).

Definition my_a := 2.
Eval cbv beta in (my_a).
Eval cbv delta in (my_a).

Eval cbv delta in (match true with true => true | false => false end).
Eval cbv iota in (match true with true => true | false => false end).

Variable n : nat.
Eval cbv delta beta iota in (1 + n).
Compute (n + 1).

Print Nat.add.

Print eq.
Check prod_ind.
Check eq_ind.

Print True.
Check eq_ind.
Definition false_not_true : (false = true) -> False :=
  fun (H : false = true) =>
    eq_ind false                                (* x is false *)
           (fun x => if x then False else True) (* P *)
           I                                    (* P x is True and I : True *)
           true                                 (* y is false *)
           H.                                   (* H : x = y hypothesis *)
(* P true := False *)

Variable A B : Type.
Variable p : A * B.

Check (eq_refl p) : p = p.
Fail Check (eq_refl p) : (fst p, snd p) = p.

Variable a : A.
Variable b : B.
Check (eq_refl (a, b)) : (a, b) = (a, b).
Check (eq_refl (a, b)) : (fst (a, b), snd (a, b)) = (a, b).

Check prod_ind.
Check  fun (p : A * B) =>
    prod_ind (fun q => (fst q, snd q) = q).

Definition fst_snd_p_eq_p : forall p : (A * B), (fst p, snd p) = p :=
  fun (p : A * B) =>
    prod_ind (fun q => (fst q, snd q) = q)
             (fun a b => eq_refl (a, b))
             p.

Variable C : (A * B) -> Type.
Variable h : C (fst p, snd p).
Fail Check (h : C p).

Definition transport A B (H : A = B) (x : A) : B :=
  eq_rect A
         (fun x => x)
         x
         B
         H.

Definition func_presv_eq A B a b (f : A -> B) (H : a = b) : f a = f b :=
  eq_rect a
         (fun x => f a = f x)
         (eq_refl (f a))
         b
         H.

Search _ (?x = ?y -> ?f ?x = ?f ?y).
Check f_equal.

Definition transport_dep A (C : A -> Type) x y (H : x = y) (Hx : C x) : C y :=
  transport (C x) (C y) (func_presv_eq A Type x y C H) Hx.

Check (transport_dep (A * B) C (fst p, snd p) p (fst_snd_p_eq_p p) h).
Compute (transport_dep (A * B) C (fst p, snd p) p (fst_snd_p_eq_p p) h).

Check eq_sym.
Definition my_eq_sym A (x : A) y (H : x = y) : y = x :=
  eq_ind x
         (fun z => z = x)
         (eq_refl x)
         y
         H.

Check eq_trans.
Definition my_eq_trans A (x : A) y z (H1 : x = y) (H2 : y = z) : x = z :=
  eq_ind y
         (fun a => a = z)
         H2
         x
         (my_eq_sym A x y H1).


Check nat_ind.
Definition np1_eq_1pn n : n + 1 = 1 + n := (* 1 + n == S n *)
  nat_ind (fun x => x + 1 = 1 + x) (* P *)
          (eq_refl 1) (* P 0 *)
          (fun x (IH : x + 1 = 1 + x) =>
             (* (S x) + 1 == S (x + 1) = S (S x) *)
             func_presv_eq nat nat (x + 1) (S x) S IH )
          n.

End Eq.

(* Refine *)
Section Refine.

Variable A B : Type.
Variable a : A.
Variable b : B.
Variable p : (A * B).

Lemma refine1 : A * B.
Proof.
  refine (_ a b).
  Restart.
  refine (pair _ b).
  refine a.
Defined.

Lemma refine2 :
  (fst (a, b), snd (a, b)) = (a, b) -> (fst (a, b), snd (a, b)) = (a, b).
Proof.
  refine (fun H => _).
  refine (_ : (fst (a, b), b) = (a, b)).
  refine (_ : (fst (a, b), snd (a, b)) = (a, b)).
  revert H.
  refine (_ : (_, _) = (fst (a, b), b) -> _).
  refine (fun x => x).
Defined.

End Refine.
 
