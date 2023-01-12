From networks Require Import listidx.

Set Implicit Arguments.

Section sequences.
    

CoInductive seq (A:Type) : Type := 
  | nil : seq A
  | cons : A -> seq A -> seq A
.
 
Arguments nil {A}. 

Inductive  isinIndex {A:Type} : seq A -> nat ->  Prop :=
    | IO : forall a s, isinIndex (cons a s) O
    | IN : forall a s n,  isinIndex s n ->  isinIndex (cons a s) (S n)
. 


Lemma nil_impossible {A:Type} (n:nat) :  ~isinIndex (A:=A) nil n.
Proof.
    unfold "~". intros. inversion H. 
Qed.

Lemma step_back {A:Type} (a:A) (s:seq A) (n: nat)  : isinIndex (cons a s) (S n) -> isinIndex s n.
Proof.
    intros.  inversion H. exact H1. 
Qed.

Lemma switch {A:Type} (a0 a1:A) (s:seq A) (n: nat) : isinIndex (cons a0  (cons a1 s)) n -> isinIndex (cons a1  (cons a0 s)) n.
Proof.
    intros.  induction n.  apply IO.  apply step_back in H. induction n. apply IN. apply IO. apply step_back in H. 
    apply (IN a1 (IN a0 H)).
Qed.


Theorem add_one (A:Type) (s:seq A) (n: nat) (a:A) : isinIndex s n  -> isinIndex (cons a s) n.
Proof.
    intros. induction H. apply IO. apply (IN a0) in IHisinIndex. apply (switch IHisinIndex).
Qed.

Theorem skip_one (A:Type) (s:seq A) (n: nat) : isinIndex s (S n ) -> isinIndex s n.
Proof.
    intros. destruct s. apply nil_impossible in H. contradiction. apply step_back in H. apply (add_one a) in H. apply H.
Qed.




Definition indexOf {A:Type} (s:seq A)  := { n:nat | isinIndex s n}.
Definition index  {A:Type} {l:seq A} (i:indexOf l) := proj1_sig i.
Definition rangeproof  {A:Type} {l:seq A} (i:indexOf l) := proj2_sig i.
Definition mkIndex {A:Type} (l:seq A) (n:nat) (p:isinIndex l n) : indexOf l := (exist (fun x => isinIndex l x) n p).
(* Coercion index : indexOf >-> nat. *)


Definition makeSig (A : Type) (P : A -> Prop) (x : A) (p : P x) : sig P :=
    exist P x p.
#[global]Arguments makeSig [A]%type_scope [P]%function_scope [x] p.


(* 
Definition destructIndex {A:Type} {s:seq A} (i:indexOf s) :  
    (index i = 0) + (exists (a:A) (n:nat) (p:isinIndex (cons a s) (S n)), (index i = S n)).
Proof.
    destruct i. simpl. destruct x. auto. right.  destruct s. apply nil_impossible in i. contradiction.
    exists a. exists x.  *)
     


Theorem absurd_type : forall (A:Prop) (C:Type), A -> ~ A -> C.
Proof.
  intros A C h1 h2.
  apply False_rect.
  apply (h2 h1).
Qed.

Fixpoint trim_unpacked {A:Type} (s:seq A) (n: nat)  : isinIndex s n -> (A * seq A) := 
    match s, n return  isinIndex s n ->  (A * seq A) with
        | nil,_           => fun h : isinIndex nil n              => absurd_type _ h (nil_impossible (n:=n))
        | cons a s', S n' => fun h : isinIndex (cons a s') (S n') => trim_unpacked (step_back h)
        | cons a s', 0    => fun _                                =>  pair a s'
    end.

Definition trim {A:Type} (s:seq A) (i:indexOf s) : (A * seq A) := 
    trim_unpacked (rangeproof i)
.

Fixpoint elem_unpacked {A:Type} (s:seq A) (n: nat)  : isinIndex s n -> A := 
    match s, n return  isinIndex s n ->  A with
        | nil,_ => fun h : isinIndex nil n  => absurd_type A h (nil_impossible (n:=n))
        | cons a s', S n' => fun h :  isinIndex (cons a s') (S n') => elem_unpacked (step_back h)
        | cons a s', 0 => fun h :  isinIndex (cons a s') 0 =>  a
    end.

Definition elem {A:Type} (s:seq A) (i:indexOf s) : A := 
    elem_unpacked (rangeproof i)
.


Fixpoint tail_unpacked {A:Type} (s:seq A) (n: nat)  : isinIndex s n -> seq A := 
    match s, n return  isinIndex s n -> seq A with
        | nil,_           => fun h : isinIndex nil n  => absurd_type (seq A) h (nil_impossible (n:=n))
        | cons a s', S n' => fun h :  isinIndex (cons a s') (S n') => tail_unpacked (step_back h)
        | cons a s', 0    => fun h :  isinIndex (cons a s') 0 =>  s'
    end.

Definition tail {A:Type} (s:seq A) (i:indexOf s) : seq A := 
    tail_unpacked (rangeproof i)
.

CoFixpoint map {A B:Type} (s:seq A) (f: A->B) : seq B :=
    match s with
      | nil => nil
      | cons a t => cons (f a)  (map t f)
    end.


Inductive isPrefixOf {A:Type}  : list A  -> seq A -> Prop :=
    | prefixN : forall a l s, isPrefixOf l s -> isPrefixOf (List.cons a l) (cons a s)
    | prefixO : isPrefixOf List.nil nil
.

Fixpoint asSeq (A:Type) (l : list A) : seq A := 
    match l with
        | List.cons a l' => cons a (asSeq l')
        | List.nil => nil
    end.

Definition subseq {A:Type} (s:seq A) (P: A -> Prop) := { i:indexOf s | P (elem i)}.

End sequences.