Require Import String.

Require Import Setoid.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Decidable.

Require Import listidx.

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

Fixpoint isPrefixOf' {A:Type} (l:list A) (s: seq A) : Prop :=
    match l,s with
        | List.cons a l', cons e s' => a=e /\ isPrefixOf' l' s'
        | List.nil, nil             => True
        | _,_                       => False
    end.

Inductive isPrefixOf {A:Type}  : list A  -> seq A -> Prop :=
    | aze  : forall a l s, isPrefixOf' l s -> isPrefixOf (List.cons a l) (cons a s)
    | azez : isPrefixOf List.nil nil
.


Definition subseq {A:Type} (s:seq A) (P: A -> Prop) := { i:indexOf s | P (elem i)}.

End sequences.

Variable nodeCount : nat.
Definition node := { n:nat | n < nodeCount}.
Definition label := nat.

Section modules.

    


Variant module_io_t ( I O : Type) :=
    | m_evt_in : label -> node -> I -> module_io_t I O 
    | m_evt_out : label -> node -> O -> module_io_t I O
.

#[global]Arguments m_evt_in [I O]%type_scope _ _ _.
#[global]Arguments m_evt_out [I O]%type_scope _ _ _.

Inductive corruption_evt   :=
    | corruption : node -> corruption_evt
.


Record modulee : Type :=  {
    l : label;
    I : Type;
    O : Type;
    module_io : Type := module_io_t I O;
    module_xioc : Type := unit + module_io + corruption_evt;
    A : seq module_xioc -> Prop
}.


End modules.

Section StateMachines.

Open Scope type_scope.


Record stateMachine (I O : Type) :Type := {
    State : Type;
    S0 : State;
    transition : State -> I -> ( O * State )
}.


Fixpoint processState {I O : Type} (SM : stateMachine I O) (inputs : list I) : State SM := 
    match inputs with
        | List.nil => S0 SM
        | List.cons i inputs' => snd (transition SM (processState SM inputs') i)
    end.    
    
Fixpoint process {I O : Type} (SM : stateMachine I O) (inputs : list I) : list O := 
    match inputs with
        | List.nil => List.nil
        | List.cons i inputs' => List.cons (fst (transition SM (processState SM inputs') i))
                                          (process SM inputs') 
    end.


End StateMachines.

Section Protocols.


Variant protocol_io_t (I O : Type) :=
    | p_evt_in : node -> I -> protocol_io_t I O 
    | p_evt_out : node -> O -> protocol_io_t I O
.

#[global]Arguments p_evt_in [I]%type_scope [O]%type_scope _ _.
#[global]Arguments p_evt_out [I]%type_scope [O]%type_scope _ _.

Variant exec_evt_t  (I O : Type) (M: list modulee)  :=
    | prot : protocol_io_t I O -> exec_evt_t I O M
    | module (m : listidx.indexOf M) : module_io (nth_checked m) -> exec_evt_t I O M
    | corr : corruption_evt -> exec_evt_t I O M
.
#[global]Arguments prot [I O]%type_scope [M]%list_scope _.
#[global]Arguments module [I O]%type_scope [M]%list_scope m _.
#[global]Arguments corr [I O]%type_scope [M]%list_scope _.

Definition SMI_pred (I O : Type) (M: list modulee) (e:exec_evt_t I O M) : Prop := 
    match e with
        | prot (p_evt_in _ _) | module _ (m_evt_out _ _ _) => True
        | _ => False
    end.

Definition SMO_pred (I O : Type) (M: list modulee) (e:exec_evt_t I O M) : Prop := 
    match e with
        | prot (p_evt_out _ _) | module _ (m_evt_in _ _ _) => True
        | _ => False
    end.

Inductive SMO_T (I O : Type) (M: list modulee)  :=
    | POut (p:node) (o:O)  : SMO_T I O M
    | MIn  (m:listidx.indexOf M) (l:label) (p:node)  (i: test.I (nth_checked m)) : SMO_T I O M
.

#[global]Arguments POut [I O]%type_scope [M]%list_scope p o.
#[global]Arguments MIn  [I O]%type_scope [M]%list_scope m l p i.

Inductive SMI_T (I : Type) (M: list modulee)  :=
    | PIn (p:node) (i:I)  : SMI_T I M
    | MOut (m:listidx.indexOf M) (l:label) (p:node)  (o: test.O (nth_checked m)) : SMI_T I M
.

#[global]Arguments PIn  [I]%type_scope [M]%list_scope p i.
#[global]Arguments MOut [I]%type_scope [M]%list_scope m l p o.

Record Protocol := {
    Ip : Type;
    Op : Type;
    M : list modulee;
    protocol_io := protocol_io_t Ip Op;
    exec_evt := exec_evt_t Ip Op M;
    SMI := {e:exec_evt | SMI_pred e};
    SMO := {e:exec_evt | SMO_pred e};
    SM : stateMachine SMI SMO;
}. 

Definition isInNodeView (P:Protocol) (e:exec_evt P) (p:node) : Prop :=
    match e with 
        | prot (p_evt_in p _)  | module _ (m_evt_out _ p _)
        | prot (p_evt_out p _) | module _ (m_evt_in _ p _)  => True
        | _ => False
end.


Lemma SMI_pred_dec (P:Protocol) (e:exec_evt P) :  {SMI_pred e} + {~SMI_pred e}.
Proof. 
    unfold decidable. unfold SMI_pred. destruct e. 
    - destruct p. all: auto. 
    - destruct m0. all: auto. 
    - auto.
Qed.



Definition execs (P:Protocol) := seq (exec_evt P).

Definition compatible_spec (P:Protocol) (s:modulee) : Prop :=
    Ip P = I s /\ Op P = O s.
    
Definition spec_of (P:Protocol) := { s:modulee | compatible_spec P s}.

Definition convert_type (I I' : Type) (p_eq : I = I') (i : I ) : I' := eq_rect I (fun X => X) i I' p_eq.
Definition convert_set (I I' : Set) (p_eq : I = I') (i : I ) : I' := eq_rect I (fun X => X) i I' p_eq.

    
(* convert protocol io events into its spec io events  *)
Definition convert_io {P:Protocol} (io : protocol_io P) (s: modulee) (comp_proof : compatible_spec P s) : module_io s :=
    match io with
        | p_evt_in  n in' => m_evt_in (l s) n (convert_type (proj1 comp_proof) in')
        | p_evt_out  n out' => m_evt_out (l s) n (convert_type (proj2 comp_proof) out')
    end.


(* convert protocol execs into sequences that can be fed to its specification admissibility predicate.  *)
CoFixpoint strip_exec (P:Protocol) (s: modulee) (comp_proof : compatible_spec P s) (E: execs P) : seq (module_xioc s) :=
    match E  with
        | cons  e tl => let e' := match e with
                | module m io => inl (inl tt)
                | prot io       => inl (inr (convert_io io comp_proof))
                | corr c    => inr c
            end in cons e' (strip_exec comp_proof tl)
        | nil _     => nil (module_xioc s)
    end.

Require Import Coq.Program.Wf.


(* the sate at the nth event is the state right *before* the nth event is processed *)
(* for the recursive call is bascally a destruct on (rangeproof i) *)
Program Fixpoint state_at (P:Protocol) (E : execs P) (i: indexOf E) (p:node) {measure (index i)} : State (SM P) :=
    match index i as n return isinIndex E n -> index i = n -> State (SM P) with
        | 0     => fun _ _ => S0 (SM P) 
        | S n'  => fun (p_in : isinIndex E (S n')) (_ : index i = (S n') ) => let prev_state := (state_at (mkIndex (skip_one p_in)) p) in 
            match (SMI_pred_dec (elem i)) with 
                | left pSMI    => snd (transition (SM P) prev_state (exist _ _ pSMI))
                | right pNegSMI => prev_state
            end
    end (rangeproof i) (eq_refl (index i)).
Next Obligation. rewrite H. auto. Defined.


End Protocols.

Section Models.
    

Definition leibniz {T:Type} (x y : T) (p_eq: x = y) (P: T -> Type) : P y -> P x.
    intros. subst y. exact X. 
Defined.

(* downcast protocol execs event into events that can be fed to module m' admissibility predicate. All events that s cannot process a replaced by unit *)
Definition clamped_evt (P:Protocol) (m: listidx.indexOf (M P)) (e: exec_evt P)  : module_xioc (nth_checked m)  := 
    match e with
        | module  m' mio =>  match (Nat.eq_dec (listidx.index m) (listidx.index m')) with
            | left eq_proof => inl (inr  (leibniz (rangeproof_irreverant m m' eq_proof) module_io mio))
            | right _       => inl (inl tt)
        end
        | corr c => inr c
        | _        =>  inl (inl tt)
    end. 

Definition  module_admissible (P:Protocol) (E:execs P) : Prop := 
    forall m: (listidx.indexOf (M P)), A (map E (clamped_evt m) ).


Definition  corrupt_at (P:Protocol) (E:execs P) (i : indexOf E)  (p:node) : Prop :=
    exists (j:indexOf E), match elem j with
        | corr (corruption p) => index j < index i
        | _ => False 
        end.

Definition corrupt (P:Protocol) (E:execs P) (p:node) : Prop :=
    exists (i : indexOf E), corrupt_at i p.

Definition honest_at (P:Protocol) (E:execs P) (i : indexOf E)  (p:node) : Prop :=
    ~ corrupt_at i p.

Definition honest (P:Protocol) (E:execs P)  (p:node) : Prop :=
    ~ corrupt E p.



(* Definition honest_admissible (P:Protocol) (E:execs P) : Prop := 
    forall (i : indexOf E), match elem i with
        |  prot (p_evt_in p ip) | module _ (m_evt_out _ p ip) => 
            isPrefixOf (process (SM P) 
                                (List.cons (nth (listidx.mkIndex (listidx.IO (List.map O (M P)) (Ip P))) ip) List.nil)) 
                       (tail i)
        | _ => False
        end.  *)

    
Definition model (P:Protocol) (E:execs P) : Prop := module_admissible E.


Definition satisfies (P: Protocol)  (s:spec_of P) (s: modulee ) (comp_proof : compatible_spec P s) : Prop  :=
    forall E:execs P, model E -> A (strip_exec comp_proof E)
.

End Models.

