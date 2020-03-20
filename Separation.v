Require Import Events. 
Require Import TraceModel. 
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import Setoid.
Require Import ClassicalExtras.
Require Import Logic.ClassicalFacts.
Require Import ZArith.
Require Import List.

Axiom L : language.

Definition ϕ_par := par L.
Definition ϕ_prg := prod nat (prg L).
Definition ϕ_ctx i := prod nat (ctx L i).
Definition ϕ_plug i : ϕ_par i -> ϕ_ctx i -> ϕ_prg :=
  fun P C =>  (fst C , plug L P (snd C)).

Lemma omega_fact : forall n m, n <= m -> (S n) <= (S m).
Proof. intros n m h. omega. Qed.

Fixpoint take_n_of_stream {A: Type} (s : stream) (n : nat) : list A :=
  match n, s with
  | 0, _  => nil
  | S m, scons a s' => cons a (take_n_of_stream s' m)
  end. 

Lemma take_n_of_stream_prefix {A : Type} (s : stream) (n: nat) :
  @list_stream_prefix A (take_n_of_stream s n) s.  
Proof.
  generalize dependent s. induction n; try now auto. 
  intros []; simpl. now auto.  
Qed.

Lemma take_n_of_stream_length {A : Type} (s: stream) (n: nat) :
  @length A (take_n_of_stream s n) <= n. 
Proof.
  generalize dependent s. induction n; try now auto.
  intros []; simpl; auto. apply omega_fact. now apply IHn.
Qed. 
  
Fixpoint take_n_of_list {A : Type} (l : list A) (n : nat) : list A :=
  match n, l with
  | 0, _ | _, nil => nil
  | S m, cons x xs => cons x (take_n_of_list xs m)
  end.

Lemma take_n_of_list_prefix {A : Type} (l : list A) (n : nat) :
  list_list_prefix (take_n_of_list l n) l.
Proof.
  generalize dependent l. induction n; try now auto;
  intros []; simpl; try now auto. 
Qed.

Lemma take_n_of_list_length {A : Type} (l : list A) (n : nat) :
  length (take_n_of_list l n) <= n.
Proof.
  generalize dependent l. induction n; try now auto.
  intros []; simpl; auto.
  intros []; simpl; auto. 
  omega. apply omega_fact. now apply IHn.
Qed.   
             
Definition take_n (t : trace) (n : nat) : list event :=
  match t with
  | tstop l _ | tsilent l => take_n_of_list l n 
  | tstream s             => take_n_of_stream s n
  end.

Lemma take_n_prefix (t : trace) (n: nat) :
  prefix (ftbd (take_n t n)) t.
Proof.
  destruct t; 
    [ now apply take_n_of_list_prefix
    | now apply take_n_of_list_prefix
    | now apply take_n_of_stream_prefix].       
Qed.

Lemma take_n_lenght (t : trace) (n : nat): length (take_n t n) <= n.
Proof.
  destruct t;
    [ now apply take_n_of_list_length
    | now apply take_n_of_list_length
    | now apply take_n_of_stream_length].
Qed.
  
Lemma list_list_prefix_shorter {A : Type} : forall l1 l2 : list A,
  list_list_prefix l1 l2 -> length l1 <= length l2.
Proof.
  induction l1; intros l2 Hpref.
  + simpl. omega.
  + destruct l2; inversion Hpref; subst. simpl.
    apply omega_fact. now apply IHl1.
Qed. 

Definition ϕ_sem : ϕ_prg -> prop :=
  fun P =>
  (fun t : trace =>
     exists l es, t = tstop l es  /\ psem (snd P) (ftbd l) /\ length l <= (fst P)).

Section Itf.
  Context {i : int L}.

Lemma non_empty_ϕ : forall P, exists t, ϕ_sem P t.
Proof.
  intros [n Pl].
  destruct (non_empty_sem L Pl) as [t HsemL]. 
  exists (tstop (take_n t n) an_endstate). unfold ϕ_sem.
  exists (take_n t n), an_endstate. simpl. repeat (split; try now auto).
  exists t. split; try now auto.   
  + now apply take_n_prefix.
  + now apply take_n_lenght. 
Qed.

Lemma leq_trans : forall n1 n2 n3, n1 <= n2 -> n2 <= n3 -> n1 <= n3.
Proof. intros n1 n2 n3 h1 h2. omega. Qed.

(* intuition there in t in sem longer than m *)
Lemma psem_consequence : forall C P t l,
    ϕ_sem (ϕ_plug i P C) t ->
    prefix (ftbd l) t ->
    length l <= fst C.
Proof.
  intros [n C] P t m [mm [es [hem [h1 h2]]]] hpref. subst. 
  simpl in *. apply (leq_trans (length m) (length mm) n); auto.   
  now apply list_list_prefix_shorter.   
Qed.

Definition ϕ := Build_language ϕ_par ϕ_ctx ϕ_plug
                               ϕ_sem
                               non_empty_ϕ.


(**********************************************************)
(* RSP =/=> RTP                                           *)
(**********************************************************)

Definition c : par ϕ i -> par L i :=
  fun P => P.

Definition c_RPP (P : par ϕ i) (π : prop) : Prop :=
  rsat P π -> rsat (c P) π.

Lemma C_robustly_safety : forall P S, Safety S -> c_RPP P S.
Proof.
  intros P S Hsafety. unfold c_RPP. rewrite contra.
  unfold rsat. repeat rewrite not_forall_ex_not.
  intros [C hC]. unfold sat in *. rewrite not_forall_ex_not in *.
  destruct hC as [t hh]. rewrite not_imp in hh.
  destruct hh as [h1 h2]. destruct (Hsafety t h2) as [m [hpref hwit]]. 
  destruct m.
  + exists (length l, C). intros ff. simpl in ff.
    destruct t; inversion hpref; subst.
    apply (hwit (tstop l0 e)); auto.
    apply ff. unfold ϕ_sem, ϕ_plug; simpl. 
    exists l0, e. repeat (split; try now auto).
    exists (tstop l0 e). split; auto. simpl. now apply list_list_prefix_ref. 
  + exists (length l, C). intros ff. simpl in ff.
    apply (hwit (tstop l an_endstate)); auto.
    simpl. now apply list_list_prefix_ref.   
    apply ff. unfold ϕ_sem, ϕ_plug; simpl.
    exists l, an_endstate. repeat (split; try now auto).
    now exists t. 
Qed.

(*
  WHILE true
   an_envet;
  END.
 *)
Definition an_omega := constant_stream (an_event).
Definition another_omega := constant_stream (another_event).

Hypothesis an_omega_produced : exists P, forall C, sem L (@plug L i P C) (tstream an_omega).
Hypothesis another_omega_produced : exists P, forall C, sem L (@plug L i P C) (tstream another_omega).

Lemma not_equal: ~ stream_eq an_omega another_omega.
Proof.   
  rewrite stream_eq_finetely_refutable. 
  exists nil, an_event, another_event. 
  repeat (split; try now auto).
  now apply different_events.
Qed.

Definition my_pi :=
  fun t =>
    match t with
    | tstream s  => stream_eq s an_omega
    | _ => True
    end. 

Lemma my_pi_dense : Dense my_pi.
Proof.
  intros t Hfin. destruct t; now inversion Hfin. 
Qed.

Lemma another_omega_not_in_my_pi : ~ my_pi (tstream another_omega).
Proof.
 simpl. intros H.  apply stream_eq_sym in H. now apply not_equal. 
Qed.

Lemma cut_lemma : forall C P t, sem ϕ (@plug ϕ i P C) t -> fin t.
Proof.
  intros C P t H. simpl in*.
  unfold ϕ_sem, ϕ_plug in *. destruct H as [m [es [hp H]]].
  now rewrite hp. 
Qed.

Axiom some_ctx_L : ctx L i.

Theorem separation_RSP_RDP :
  (forall P π, Safety π -> c_RPP P π) /\
  ~  (forall P π, Dense π -> c_RPP P π).
Proof.
  split.
  + now apply C_robustly_safety.
  + intros ff. destruct another_omega_produced as [P H].
    specialize (ff P my_pi). unfold c_RPP, rsat, sat in ff.
    simpl in ff.
    assert (hh :  (forall (C : ctx ϕ i) (t : trace), sem ϕ (ϕ_plug i P C) t -> my_pi t)).
    { intros C t H0. simpl in H0. unfold ϕ_sem, ϕ_plug in H0.
      destruct H0 as [m [e [hm H0]]]. now rewrite hm. }
    specialize (ff my_pi_dense hh).  specialize (ff some_ctx_L (tstream another_omega)).
    assert (sem L (some_ctx_L [P]) (tstream another_omega)) by now apply (H some_ctx_L).
    specialize (ff H0). now apply another_omega_not_in_my_pi.
Qed.

Theorem separation_RSP_RTP : (forall P π, Safety π -> c_RPP P π) /\ ~  (forall P π, c_RPP P π).
Proof.
  split.
  + now apply C_robustly_safety.
  + intros ff. destruct another_omega_produced as [P H].
    destruct separation_RSP_RDP as [K1 K2].
    now apply K2.
Qed.

(**********************************************************)
(* RDP =/=> RTP                                           *)
(**********************************************************)

Hypothesis only_an_omega_produced : exists P, forall C,
      (sem L (plug L P C) (tstream an_omega) /\
       (forall t, sem L (@plug L i P C) t ->
         (exists s, t = tstream s /\ stream_eq s an_omega))).   


Definition c2 : par L i -> par ϕ i :=
  fun P => P.

Definition c2_RPP (P : par L i) (π : prop) : Prop :=
  rsat P π -> rsat (c2 P) π.

Lemma c2_robustly_dense: forall P π, Dense π -> c2_RPP P π.
Proof.
  intros P π hl. unfold c2_RPP, rsat, sat.
  intros h0 [n C] t hsem.
  simpl in hsem.
  unfold ϕ_sem, ϕ_plug in hsem.
  destruct hsem as [l [es [hembed [hpsem hlen]]]].
  subst. now apply hl.  
Qed.


Definition my_pi2 : prop :=
  fun t =>
    match t with
    | tstream s => stream_eq s an_omega
    | _ => False
    end. 


Theorem separation_RDP_RTP :
  (forall P π, Dense π -> c2_RPP P π) /\
  ~  (forall P π, c2_RPP P π).
Proof.
  split.
  + now apply c2_robustly_dense.
  + intros ff. destruct only_an_omega_produced as [P h].
    specialize (ff P my_pi2).
    unfold c2_RPP, rsat, sat in ff. 
    assert (H : forall (C : ctx L i) (t : trace), sem L (C [P]) t -> my_pi2 t).
    { intros C t hsem. specialize (h C). destruct h as [h1 h2].
      destruct (h2 t hsem) as [s [H1 H2]]; now subst. }
    specialize (ff H (0, some_ctx_L) (tstop nil an_endstate)).
    assert  (sem ϕ ((0, some_ctx_L) [c2 P]) (tstop nil an_endstate)).
    { simpl. unfold ϕ_sem, ϕ_plug. exists nil, an_endstate. 
      repeat (split; try now auto). simpl. 
      exists (tstream an_omega).  
      split; try now auto. now apply (h some_ctx_L). } 
    specialize (ff H0). inversion ff.    
Qed.

Require Import TopologyTrace.

Lemma RDP_plus_RSP_RTP :
  (forall P π, Dense π -> c2_RPP P π) ->
  (forall P π, Safety π -> c2_RPP P π) ->
  (forall P π, c2_RPP P π).
Proof.
  intros h1 h2 P π. destruct (decomposition_safety_dense π) as
      [s [l [hs [hl h]]]]. unfold c2_RPP, rsat, sat in *.
  intros hh C t hsem. rewrite (h t).
  assert (hhs : forall C t, sem L (C [P]) t -> s t) by now firstorder.
  assert (hhl : forall C t, sem L (C [P]) t -> l t) by now firstorder.
  split.
  + now apply (h2 P s hs hhs C t hsem).
  + now apply (h1 P l hl hhl C t hsem).
Qed.

Corollary separation_RLP_RSP :
   (forall P π, Dense π -> c2_RPP P π) /\
   ~  (forall P π, Safety π ->  c2_RPP P π).
Proof.
  split.
  + now apply c2_robustly_dense.
  + intros ff.
    assert (forall P π, c2_RPP P π).
    { apply RDP_plus_RSP_RTP. now apply c2_robustly_dense. auto. }
    destruct separation_RDP_RTP; now auto.
Qed.

End Itf.
