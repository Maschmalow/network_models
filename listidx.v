Require Import List.
Require Import Coq.Program.Equality.

Section list_checked.

Set Implicit Arguments.

Variable A: Type.

Inductive  isinIndex  : list A -> nat ->  Prop :=
    | IO : forall l a,    isinIndex (cons a l) O
    | IN : forall l n a,  isinIndex l n ->  isinIndex (cons a l) (S n)
.

Definition indexOf  (l:list A)  := { n:nat | isinIndex l n}.
Definition index  {l:list A} (i:indexOf l) := proj1_sig i.
Definition rangeproof  {l:list A} (i:indexOf l) := proj2_sig i.
Definition mkIndex (l:list A) (n:nat) (p:isinIndex l n) : indexOf l := (exist (fun x => isinIndex l x) n p).


Lemma nil_impossible (n:nat) :  ~isinIndex nil n.
Proof.
    unfold "~". intros. inversion H. 
Qed.

Definition absurd_type {B:Prop} (C:Type):  B -> ~ B -> C.
Proof.
  intros h1 h2.
  apply False_rect.
  apply (h2 h1).
Qed.

Lemma step_back  (a:A) (l:list A) (n: nat)  : isinIndex (cons a l) (S n) -> isinIndex l n.
Proof.
    intros.  inversion H. exact H1. 
Qed.

Lemma switch  (a0 a1:A) (l:list A) (n: nat) : isinIndex (cons a0  (cons a1 l)) n -> isinIndex (cons a1  (cons a0 l)) n.
Proof.
    intros.  induction n.  apply IO.  apply step_back in H. induction n. apply IN. apply IO. apply step_back in H. 
    apply (IN a1 (IN a0 H)).
Qed.

Theorem add_one (l:list A) (n: nat) (a:A) : isinIndex l n  -> isinIndex (cons a l) n.
Proof.
    intros. induction H. apply IO. apply (IN a0) in IHisinIndex. apply (switch IHisinIndex).
Qed.


Theorem skip_one (l:list A) (n: nat) : isinIndex l (S n ) -> isinIndex l n.
Proof.
    intros. destruct l. apply nil_impossible in H. contradiction. apply step_back in H. apply (add_one a) in H. apply H.
Qed.


Fixpoint nth_checked_unpacked  (l:list A) (n: nat) {struct n}  : isinIndex l n -> A := 
    match l, n return  isinIndex l n ->  A with
        | nil, _          => fun (h : isinIndex nil n)  => absurd_type A h (nil_impossible (n:=n)) 
        | cons a l', S n' => fun (h :  isinIndex (cons a l') (S n')) => nth_checked_unpacked (step_back h)
        | cons a l', 0    => fun _ =>  a
    end.

Definition nth_checked  {l:list A} (i:indexOf l) : A := 
    nth_checked_unpacked (rangeproof i)
.

Lemma ind_step_mhh   (l:list A) (n: nat) (a:A) :
    nth_error l n = nth_error (a :: l) (S n) .
Proof.
    destruct nth_error. auto. auto.
Qed.  



Lemma ind_step   (l:list A) (n: nat) (a:A) (p: isinIndex (a :: l) (S n)) :
    exists p' : isinIndex l n, nth_checked_unpacked p = nth_checked_unpacked p'.
Proof.
    exists (step_back p). simpl. trivial.
Qed. 


Theorem nth_in_or_error  {l:list A} (n: nat) (p : isinIndex l n) : nth_error l n =  Some (nth_checked_unpacked p).
Proof.
    generalize p. induction p.
        - intros. unfold nth_error. unfold nth_checked_unpacked. auto.
        - intros.  pose (ind_step_mhh l n a). rewrite <- e. clear e. pose (ind_step p0). destruct e. rewrite -> H. apply (IHp x).
Qed. 


Corollary rangeproof_irreverant  {l:list A} (i1 i2:indexOf l) (p_eq : index i1 = index i2) : nth_checked i1 = nth_checked i2.
Proof.
    unfold nth_checked. cut (Some (nth_checked_unpacked (rangeproof i1)) =
    Some (nth_checked_unpacked (rangeproof i2))). intros. injection H. trivial.
    rewrite <- (nth_in_or_error (rangeproof i1)). rewrite <- (nth_in_or_error (rangeproof i2)).
    auto.
Qed.




End list_checked.
