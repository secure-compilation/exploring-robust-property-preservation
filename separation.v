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
Definition ϕ_ctx  := prod nat (ctx L).
Definition ϕ_plug : ϕ_par -> ϕ_ctx -> ϕ_prg :=
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


(* Fixpoint take_nth_pref (t : trace) (n : nat) : finpref := *)
(*   match n, t with *)
(*   | 0, _ | _ ,tstop | _, tsilent => ftbd *)
(*   | S m, tcons x xs => fcons x (take_nth_pref xs m) *)
(*   end.                            *)    

(* Lemma nth_pref_pref : forall t n, prefix (take_nth_pref t n) t. *)
(* Proof. *)
(*   intros t n. generalize dependent t. induction n; intros t; try now auto. *)
(*   destruct t; simpl in *; try now auto.  *)
(* Qed.  *)

(* Lemma pref_take_pref : forall m t, *)
(*     prefix m t -> *)
(*     prefix m (take_n t (length m)). *)
(* Proof. *)
(*   intros m t. generalize dependent t. destruct m as [m | m]; induction m; intros t hpref; try now auto. *)
(*   + destruct t; try now auto. *)
(*   + destruct t; try now auto. *)
(*     simpl in *. destruct hpref as [h1 h2]. split; try now auto. *)
(*   + destruct t; try now auto. *)
(*     simpl in *; destruct hpref as [h1 h2]. split; try now auto. *)
(* Qed.    *)

(* Lemma take_embedding : forall t m, *)
(*     prefix m t -> *)
(*     exists es, (take_n t (length m)) = embedding es m. *)
(* Proof. *)
(*   intros t m. generalize dependent t. *)
(*   destruct m as [m | m]; induction m; intros t hpref; simpl in *; *)
(*     destruct t; subst; try now eauto. *)
(*   - destruct hpref as [h1 h2]; subst. *)
(*     specialize (IHm t h2). destruct IHm as [es Hes]. now rewrite Hes. *)
(*   - destruct hpref as [h1 h2]; subst. *)
(*     destruct (IHm t h2) as [es Hes]. eexists; now rewrite Hes. *)
(* Qed.  *)

Definition ϕ_sem : ϕ_prg -> prop :=
  fun P =>
  (fun t : trace =>
     exists l es, t = tstop l es  /\ psem (snd P) (ftbd l) /\ length l <= (fst P)).

  
(*   intros n. induction n; intros t; try now auto. *)
(*   destruct t; simpl; try now auto. *)
(*   + omega. *)
(*   + omega. *)
(*   + apply omega_fact. now apply IHn. *)
(* Qed. *)

(* Lemma length_smaller : forall P t, *)
(*     sem L (snd P) t -> length (take_nth_pref t (fst P)) <= fst P. *)
(* Proof. *)
(*   intros P t hsem. now apply length_take_n. *)
(* Qed. *)

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

(* Lemma fpr_shorter: forall m1 m2, fpr m1 m2 -> length m1 <= length m2. *)
(* Proof. *)
(*   destruct m1 as [m1 | m1]; induction m1; intros m2 hpref; simpl; try omega. *)
(*   + destruct m2; try now auto. inversion hpref; subst. *)
(*     simpl. apply omega_fact. omega. *)
(*   + destruct m2 as [m2 | m2]; destruct m2; try now auto. *)
(*     ++ simpl. inversion hpref; subst. *)
(*        apply omega_fact. now apply (IHm1 (fstop m2 an_endstate) H0). *)
(*     ++ simpl. inversion hpref; subst. *)
(*        apply omega_fact. now apply (IHm1 (ftbd m2) H0). *)
(* Qed. *)
  
(* (*TODO : move to Tracemdel.v *)          *)
(* Lemma prefix_embeding_fpr : forall m1 m2 es, *)
(*     prefix m1 (embedding es m2) -> fpr m1 (m2[fstop es/ftbd]). *)
(* Proof. *)
(*   destruct m1 as [m1 | m1]; induction m1; intros [m2 | m2]; intros es hpref; try now auto; *)
(*     try now destruct m2. *)
(*   + destruct m2; try now auto. inversion hpref. subst. *)
(*     simpl. specialize (IHm1 (fstop m2 e0) e H0). destruct IHm1; now subst. *)
(*   + destruct m2; try now auto. inversion hpref. subst. *)
(*     simpl. specialize (IHm1 (fstop m2 es) e H0). destruct IHm1; now subst. *)
(*   + destruct m2; try now auto. inversion hpref. subst. *)
(*     simpl. specialize (IHm1 (fstop m2 e) es H0). simpl in *; now subst.   *)
(*   + destruct m2; try now auto. inversion hpref. subst. *)
(*     simpl. specialize (IHm1 (fstop m2 es) es H0). simpl in *; now subst. *)
(* Qed. *)

Lemma leq_trans : forall n1 n2 n3, n1 <= n2 -> n2 <= n3 -> n1 <= n3.
Proof. intros n1 n2 n3 h1 h2. omega. Qed.

(* intuition there in t in sem longer than m *)
Lemma psem_consequence : forall C P t l,
    ϕ_sem (ϕ_plug P C) t ->
    prefix (ftbd l) t ->
    length l <= fst C.
Proof.
  intros [n C] P t m [mm [es [hem [h1 h2]]]] hpref. subst. 
  simpl in *. apply (leq_trans (length m) (length mm) n); auto.   
  now apply list_list_prefix_shorter.   
Qed.

Definition ϕ := Build_language ϕ_plug
                            ϕ_sem
                            non_empty_ϕ.


(**********************************************************)
(* RSP =/=> RPP                                           *)
(**********************************************************)

Definition c : par ϕ -> par L :=
  fun P => P.

Definition c_RPP (P : par ϕ) (π : prop) : Prop :=
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

Hypothesis an_omega_produced : exists P, forall C, sem L (plug L P C) (tstream an_omega).
Hypothesis another_omega_produced : exists P, forall C, sem L (plug L P C) (tstream another_omega).

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
    | tstop _ _ => True
    | tstream s  => stream_eq s an_omega
    | _ => False
    end. 

Lemma my_pi_liveness : Liveness my_pi.
Proof.
  apply all_fin_in_all_liv. intros t Hfin. destruct t; now inversion Hfin. 
Qed.

Lemma another_omega_not_in_my_pi : ~ my_pi (tstream another_omega).
Proof.
 simpl. intros H.  apply stream_eq_sym in H. now apply not_equal. 
Qed.

Lemma cut_lemma : forall C P t, sem ϕ (plug ϕ P C) t -> fin t.
Proof.
  intros C P t H. simpl in*.
  unfold ϕ_sem, ϕ_plug in *. destruct H as [m [es [hp H]]].
  now rewrite hp. 
Qed.

Axiom some_ctx_L : ctx L.

Theorem separation_RSP_RLP :
  (forall P π, Safety π -> c_RPP P π) /\
  ~  (forall P π, Liveness π -> c_RPP P π).
Proof.
  split.
  + now apply C_robustly_safety.
  + intros ff. destruct another_omega_produced as [P H].
    specialize (ff P my_pi). unfold c_RPP, rsat, sat in ff.
    simpl in ff.
    assert (hh :  (forall (C : ctx ϕ) (t : trace), sem ϕ (ϕ_plug P C) t -> my_pi t)).
    { intros C t H0. simpl in H0. unfold ϕ_sem, ϕ_plug in H0.
      destruct H0 as [m [e [hm H0]]]. now rewrite hm. }
    specialize (ff my_pi_liveness hh).  specialize (ff some_ctx_L (tstream another_omega)).
    assert (sem L (some_ctx_L [P]) (tstream another_omega)) by now apply (H some_ctx_L).
    specialize (ff H0). now apply another_omega_not_in_my_pi.
Qed.

Theorem separation_RSP_RPP : (forall P π, Safety π -> c_RPP P π) /\ ~  (forall P π, c_RPP P π).
Proof.
  split.
  + now apply C_robustly_safety.
  + intros ff. destruct another_omega_produced as [P H].
    destruct separation_RSP_RLP as [K1 K2].
    now apply K2.
Qed.

(**********************************************************)
(* RLP =/=> RPP                                           *)
(**********************************************************)

Hypothesis only_an_omega_produced : exists P, forall C,
      (sem L (plug L P C) an_omega /\
      (forall t, sem L (plug L P C) t -> t_eq t an_omega)).

Definition c2 : par L -> par ϕ :=
  fun P => P.

Definition c2_RPP (P : par L) (π : prop) : Prop :=
  rsat P π -> rsat (c2 P) π.

Lemma c2_robustly_liveness: forall P π, Liveness π -> c2_RPP P π.
Proof.
  intros P π hl. unfold c2_RPP, rsat, sat.
  intros h0 [n C] t hsem.
  simpl in hsem.
  unfold ϕ_sem, ϕ_plug in hsem.
  destruct hsem as [m [hembed [hpsem hlen]]].
  subst. apply all_fin_in_all_liv; try now auto.
  now apply embed_fin.
Qed.


Definition my_pi2 : prop :=
  fun t => t_eq t an_omega.


(* the trick to unfold cofixpoint *)
Definition frob (t : trace) : trace :=
  match t with
  | tstop es => tstop es
  | tsilent => tsilent
  | tcons e t' => tcons e t'
  end.

Theorem frob_eq : forall (t : trace), t = frob t.
  destruct t; reflexivity.
Qed.


Theorem separation_RLP_RPP :
  (forall P π, Liveness π -> c2_RPP P π) /\
  ~  (forall P π, c2_RPP P π).
Proof.
  split.
  + now apply c2_robustly_liveness.
  + intros ff. destruct only_an_omega_produced as [P h].
    specialize (ff P my_pi2).
    unfold c2_RPP, rsat, sat in ff.
    assert (H : forall (C : ctx L) (t : trace), sem L (C [P]) t -> my_pi2 t).
    { intros C t hsem. specialize (h C). destruct h as [h1 h2].
      now apply h2. }
    specialize (ff H (0, some_ctx_L) (tstop an_endstate)).
    assert  (sem ϕ ((0, some_ctx_L) [c2 P]) (tstop an_endstate)).
    simpl. unfold ϕ_sem, ϕ_plug. exists (ftbd nil). 
    repeat (split; try now auto). simpl. exists an_endstate. repeat (split; try now auto).
    exists an_omega.
    split; try now auto. now apply (h some_ctx_L).
    specialize (ff H0). unfold my_pi2 in ff. inversion ff.
    unfold an_omega in H0.
    assert (forall e, constant_trace e = tcons e (constant_trace e)).
    { clear.
      intros e. remember (constant_trace e) as t.
      rewrite (frob_eq t) at 1. subst. reflexivity.
    }
    subst. 
    specialize (H1 an_event).
    simpl in *.
    unfold an_omega in H3.
    rewrite H1 in H3. inversion H3.      
Qed.

Require Import TopologyTrace.

Lemma RLP_plus_RSP_RPP :
  (forall P π, Liveness π -> c2_RPP P π) ->
  (forall P π, Safety π -> c2_RPP P π) ->
  (forall P π, c2_RPP P π).
Proof.
  intros h1 h2 P π. destruct (decomposition_safety_liveness π) as
      [s [l [hs [hl h]]]]. unfold c2_RPP, rsat, sat in *.
  intros hh C t hsem. rewrite (h t).
  assert (hhs : forall C t, sem L (C [P]) t -> s t) by now firstorder.
  assert (hhl : forall C t, sem L (C [P]) t -> l t) by now firstorder.
  split.
  + now apply (h2 P s hs hhs C t hsem).
  + now apply (h1 P l hl hhl C t hsem).
Qed.

Corollary separation_RLP_RSP :
   (forall P π, Liveness π -> c2_RPP P π) /\
   ~  (forall P π, Safety π ->  c2_RPP P π).
Proof.
  split.
  + now apply c2_robustly_liveness.
  + intros ff.
    assert (forall P π, c2_RPP P π).
    { apply RLP_plus_RSP_RPP. now apply c2_robustly_liveness. auto. }
    destruct separation_RLP_RPP as [K1 K2]. now auto.
Qed.
