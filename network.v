Require Import String.

(* Require Import Setoid. *)
(* Require Import Coq.Arith.PeanoNat. *)
(* Require Import Coq.Logic.Decidable. *)


From networks Require Import listidx.
From networks Require Import sequences.

Set Implicit Arguments.


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


Record module : Type :=  {
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


End StateMachines.

Section Protocols.


Variant protocol_io_t (I O : Type) :=
    | p_evt_in : node -> I -> protocol_io_t I O 
    | p_evt_out : node -> O -> protocol_io_t I O
.

#[global]Arguments p_evt_in [I]%type_scope [O]%type_scope _ _.
#[global]Arguments p_evt_out [I]%type_scope [O]%type_scope _ _.



Variant exec_evt_t  (I O : Type) (M: list module)  :=
    | prot : protocol_io_t I O -> exec_evt_t I O M
    | mod (m : listidx.indexOf M) : module_io (nth_checked m) -> exec_evt_t I O M
    | corr : corruption_evt -> exec_evt_t I O M
.


#[global]Arguments prot [I O]%type_scope [M]%list_scope _.
#[global]Arguments mod [I O]%type_scope [M]%list_scope m _.
#[global]Arguments corr [I O]%type_scope [M]%list_scope _.
(*
 Definition in_SMI_t (I O : Type) (M: list module) (e:exec_evt_t I O M) : Prop := 
    match e with
        | prot (p_evt_in _ _) | mod _ (m_evt_out _ _ _) => True
        | _ => False
    end.

Definition in_SMO_t (I O : Type) (M: list module) (e:exec_evt_t I O M) : Prop := 
    match e with
        | prot (p_evt_out _ _) | mod _ (m_evt_in _ _ _) => True
        | _ => False
    end. *)


Record Protocol := {
    Ip : Type;
    Op : Type;
    M : list module;
    protocol_io := protocol_io_t Ip Op;
    exec_evt := exec_evt_t Ip Op M; 
    prot_p := prot (I:=Ip) (O:=Op) (M:=M);
    module_p := mod (I:=Ip) (O:=Op) (M:=M);
    corr_p := corr (I:=Ip) (O:=Op) (M:=M);
    (* inSMI := in_SMI_t (I:=Ip) (O:=Op) (M:=M);
    inSMO := in_SMO_t (I:=Ip) (O:=Op) (M:=M); *)

    (* all definitions required to define the state machine I/O types needs to be inlined within the record def*)
    inSMI := fun (e:exec_evt) => match e with
                | prot (p_evt_in _ _) | mod _ (m_evt_out _ _ _) => True
                | _ => False
            end;
    inSMO := fun (e : exec_evt) =>  match e with
                | prot (p_evt_out _ _) | mod _ (m_evt_in _ _ _) => True
                | _ => False
              end;
    SMI := {e:exec_evt | inSMI e};
    SMO := list {e:exec_evt | inSMO e};
    SM : stateMachine SMI SMO;
}. 



(* in view of p means it's an input/output of p  *)
Definition isInNodeView (P:Protocol) (e:exec_evt P) (p:node) : Prop :=
    match e with 
        | prot (p_evt_in p _)  | mod _ (m_evt_out _ p _)
        | prot (p_evt_out p _) | mod _ (m_evt_in _ p _)  => True
        | _ => False
end.




Lemma view_subset_SMIO (P:Protocol) (e:exec_evt P) (p:node) : isInNodeView e p -> {inSMI e} + {inSMO e} .
Proof.
    intros. unfold isInNodeView in H. 
    repeat match goal with 
    | s : match ?a with _ => _ end |- _ =>  destruct a 
    end.
    all: simpl;auto.
Qed.

Lemma isInNodeView_dec (P:Protocol) (e:exec_evt P) (p:node) : {isInNodeView e p} + {~isInNodeView e p}.
Proof.
    unfold isInNodeView. destruct e.
    - destruct p0. all: auto.
    - destruct m0. all: auto.
    - auto.
Qed.

Lemma in_SMI_dec (P:Protocol) (e:exec_evt P) :  {inSMI e} + {~inSMI e}.
Proof. 
    unfold inSMI. destruct e. 
    - destruct p. all: simpl;auto. 
    - destruct m0. all: simpl;auto. 
    - auto.
Qed.



Definition execs (P:Protocol) := seq (exec_evt P).

Definition compatible_spec (P:Protocol) (s:module) : Prop :=
    Ip P = I s /\ Op P = O s.
    
Definition spec_of (P:Protocol) := { s:module | compatible_spec P s}.

Definition convert_type (I I' : Type) (p_eq : I = I') (i : I ) : I' := eq_rect I (fun X => X) i I' p_eq.
Definition convert_set (I I' : Set) (p_eq : I = I') (i : I ) : I' := eq_rect I (fun X => X) i I' p_eq.

    
(* convert protocol io events into its spec io events  *)
Definition convert_io {P:Protocol} (io : protocol_io P) (s: module) (comp_proof : compatible_spec P s) : module_io s :=
    match io with
        | p_evt_in  n in' => m_evt_in (l s) n (convert_type (proj1 comp_proof) in')
        | p_evt_out  n out' => m_evt_out (l s) n (convert_type (proj2 comp_proof) out')
    end.


(* convert protocol execs into sequences that can be fed to its specification admissibility predicate.  *)
CoFixpoint strip_exec (P:Protocol) (s: module) (comp_proof : compatible_spec P s) (E: execs P) : seq (module_xioc s) :=
    match E  with
        | cons  e tl => let e' := match e with
                | mod m io => inl (inl tt)
                | prot io       => inl (inr (convert_io io comp_proof))
                | corr c    => inr c
            end in cons e' (strip_exec comp_proof tl)
        | nil _     => nil (module_xioc s)
    end.

Require Import Coq.Program.Wf.


(* the sate at the nth event is the state right *before* the nth event is processed by the SM*)
(* the recursive call is bascally a destruct on (rangeproof i) *)
(* You may notice that "index i = n" is unused. It is present to make it appear as an hypothesis of the proof of well-foundedness *)
Program Fixpoint state_at (P:Protocol) (E : execs P) (i: indexOf E) (p:node) {measure (index i)} : State (SM P) :=
    match index i as n return isinIndex E n -> index i = n -> State (SM P) with
        | 0     => fun _ _ => S0 (SM P) 
        | S n'  => fun (p_in : isinIndex E (S n')) (_ : index i = (S n') ) => let prev_state := (state_at (mkIndex (skip_one p_in)) p) in 
            match (in_SMI_dec (elem i)), (isInNodeView_dec (elem i) p) with  (* only process input in view *)
                | left pSMI, left pNodeView => snd (transition (SM P) prev_state (exist _ _ pSMI))
                | _, _                      => prev_state
            end
    end (rangeproof i) (eq_refl (index i)).
Next Obligation. rewrite H. auto. Defined.




Definition isNodeOut (P:Protocol) (e:exec_evt P) (p:node) : Prop := 
    match e with 
    | prot (p_evt_out p _) | mod _ (m_evt_in _ p _)  => True
    | _ => False
end.

Definition isNodeIn  (P:Protocol) (e:exec_evt P) (p:node) : Prop := 
    match e with 
        | prot (p_evt_in p _)  | mod _ (m_evt_out _ p _) => True
        | _ => False
end.

Lemma NodeOutEquivSMOView  (P:Protocol) (e:exec_evt P) (p:node) : isInNodeView e p /\ inSMO e <-> isNodeOut e p.
Proof.
    split. all:intros.
    - unfold isNodeOut. destruct H. unfold isInNodeView in H. unfold inSMO in H0.  
        repeat match goal with 
        | s : match ?a with _ => _ end |- _ =>  destruct a
        end. all: auto.
    - split. unfold isInNodeView. unfold isNodeOut in H. 
        repeat match goal with 
        | s : match ?a with _ => _ end |- _ =>  destruct a
        end. all:auto.
Qed.

Definition NodeOutConj (P:Protocol) {e:exec_evt P} {p:node}  (proof: isNodeOut e p) : isInNodeView e p /\ inSMO e :=  proj2 (NodeOutEquivSMOView e p) proof.


Lemma NodeInEquivSMIView  (P:Protocol) (e:exec_evt P) (p:node) : isInNodeView e p /\ inSMI e <-> isNodeIn e p.
split. all:intros.
- unfold isNodeIn. destruct H. unfold isInNodeView in H. unfold inSMI in H0.  
    repeat match goal with 
    | s : match ?a with _ => _ end |- _ =>  destruct a
    end. all: auto.
- split. unfold isInNodeView. unfold isNodeIn in H. 
    repeat match goal with 
    | s : match ?a with _ => _ end |- _ =>  destruct a
    end. all:auto.
Qed.
Definition NodeInConj (P:Protocol) {e:exec_evt P} {p:node}  (proof: isNodeIn e p) : isInNodeView e p /\ inSMI e :=  proj2 (NodeInEquivSMIView e p) proof.


(*The SM output of node p' SM at event i, **before** (elem i) is processed *)
Definition process_at (P:Protocol) (E : execs P) (i: indexOf E) (p:node) (pIn : isNodeIn (elem i) p)  : list {e: exec_evt P | isNodeOut e p} :=
    fst (transition (SM P) (state_at i p) (makeSig (proj2 (NodeInConj pIn)))).

Definition process_at_asSMO (P:Protocol) (E : execs P) (i: indexOf E) (p:node) (pIn : isNodeIn (elem i) p) : SMO P :=
    (process_at i p pIn) (*? is there some implicit coercions i'm not aware of? *)
.


End Protocols.

Section Models.
    

Definition leibniz {T:Type} (x y : T) (p_eq: x = y) (P: T -> Type) : P y -> P x.
    intros. subst y. exact X. 
Defined.



(* downcast protocol execs event into events that can be fed to mod m' admissibility predicate. All events that m cannot process is replaced by unit *)
Definition clamped_evt (P:Protocol) (m: listidx.indexOf (M P)) (e: exec_evt P)  : module_xioc (nth_checked m)  := 
    match e with
        | mod  m' mio =>  match (PeanoNat.Nat.eq_dec (listidx.index m) (listidx.index m')) with
            | left eq_proof => inl (inr  (leibniz (rangeproof_irreverant m m' eq_proof) module_io mio))
            | right _       => inl (inl tt)
        end
        | corr c => inr c
        | _        =>  inl (inl tt)
    end. 

Definition  module_admissible (P:Protocol) (E:execs P) : Prop := 
    forall m: (listidx.indexOf (M P)), A (map E (clamped_evt m) ).

 Definition DelayPred := forall (P:Protocol) (E:execs P) (i:indexOf E) (p:node),  Prop. 

Definition staticAdv := fun (P:Protocol) (E:execs P) (i : indexOf E)  (p:node) => True.
Definition staticAdv' : DelayPred := fun _ _ _ _ => True.

Definition  corrupt_at (P:Protocol) (E:execs P) (D: DelayPred) (i : indexOf E)  (p:node)  : Prop :=
    exists (j:indexOf E), match elem j with
        | corr (corruption p) => index j < index i /\ D P E i p
        | _ => False 
        end.

Definition corrupt (P:Protocol) (E:execs P) (D: DelayPred) (p:node) : Prop :=
    exists (i : indexOf E), corrupt_at D i p.

Definition honest_at (P:Protocol) (E:execs P) (D: DelayPred) (i : indexOf E)  (p:node)  : Prop :=
    ~ corrupt_at D i p.

Definition honest (P:Protocol) (E:execs P) (D: DelayPred) (p:node)  : Prop :=
    ~ corrupt E D p.


(* honest node admissibility : when an honest node receives input, all the following events are the node output. I.e., honest nodes follows the protocol *)
Definition honest_admissible (P:Protocol) (D: DelayPred) (E:execs P) : Prop := 
    forall (i : indexOf E), exists (p:node), forall pIn : (isNodeIn (elem i) p), honest_at D i p ->
    isPrefixOf (List.map (proj1_sig (P:=fun x=> isNodeOut x p)) (process_at i p pIn) )
               (tail i)
.
(* note to self: in this version, the adversary is NOT authorized to reorder outputs ! may need to fix *)
    



Definition corruption_struct := (node -> Prop) -> Prop.

Definition k_cover (C:corruption_struct) (k:nat) := 
    exists (pi: {n:nat | n<k} -> (node->Prop)),
    forall (p: node) (pi_n: {n:nat | n<k}),
    pi pi_n p
.

Record adversary_struct : Type := {
    C : corruption_struct;
    D : DelayPred;
}.

(* respects a given corruption structure*)
Definition structure_admissible (P:Protocol) (Adv:adversary_struct) (E:execs P)  : Prop := 
    forall (i:indexOf E), (C Adv) (corrupt_at (D Adv) i)
.

(* E is part of the model of P iff all admissibility requirements are met*)
Definition model (P:Protocol) (Adv:adversary_struct) (E:execs P) : Prop := 
    module_admissible E   /\
    honest_admissible (D Adv) E /\
    structure_admissible Adv E.


Definition satisfies (P: Protocol) (Adv:adversary_struct)  (s:spec_of P) (s: module ) (comp_proof : compatible_spec P s) : Prop  :=
    forall E:execs P, model Adv E -> A (strip_exec comp_proof E)
.

End Models.

