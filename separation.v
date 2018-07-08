Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import Setoid.
Require Import ClassicalExtras.
Require Import Logic.ClassicalFacts.
Require Import ZArith. 

CoInductive t_eq : trace -> trace -> Prop :=
| etrace : forall (e : event) t1 t2, t_eq t1 t2 -> t_eq (tcons e t1) (tcons e t2).

Lemma t_eq_symm : forall t1 t2, t_eq t1 t2 -> t_eq t2 t1.
Admitted.

Lemma prefix_preserved : forall m t1 t2, prefix m t1 -> t_eq t1 t2 -> prefix m t2.
Proof.
  intros m. induction m; intros t1 t2 hpref heq; try now auto.
  + now destruct t1, t2. 
  + destruct t1, t2; try now auto. inversion hpref. subst.   
    inversion heq. subst. simpl. split; try now auto.
    now apply (IHm t1 t2). 
Qed.

Lemma same_finite_prefixes : forall t1 t2, t_eq t1 t2 ->
                             forall m, (prefix m t1) <-> prefix m t2.
Proof.
  intros t1 t2 heq m. split; intros H;
  [now apply (prefix_preserved m t1 t2)
  |apply (prefix_preserved m t2 t1); try now auto].
  now apply t_eq_symm. 
Qed. 

Lemma neq_finitely_refutable : forall t1 t2,
    ~ (t_eq t1 t2) <-> (exists m1 m2, prefix m1 t1 /\ prefix m2 t2 /\ ~ (prefix m1 t2 /\ prefix m2 t1)).
Proof.
  intros t1 t2. split.
  - admit.
  - intros [m1 [m2 [h1 [h2 hn]]]] hf. apply hn. split.
    + now apply (same_finite_prefixes t1 t2).
    + apply t_eq_symm in hf. now apply (same_finite_prefixes t2 t1).
Admitted.


Axiom L : level. 

Definition ϕ_prg := prod nat (prg L). (* CH: So why does the program have a bound if it's just ignored? Can it be removed? *)
Definition ϕ_ctx  := prod nat (ctx L). 
Definition ϕ_plug : ϕ_prg -> ϕ_ctx -> ϕ_prg :=
  fun P C =>  (fst C , plug L (snd P) (snd C)).

Fixpoint length (m : finpref) : nat :=
  match m with
  | fstop | ftbd => 0
  | fcons x xs => S (length xs)
  end.

Lemma stop_same_lenght: forall m, length m = length (m[fstop/ftbd]). 
Proof.
  induction m; try now auto.
  simpl. now rewrite IHm.
Qed. 

Fixpoint take_n (t : trace) (n : nat) : trace :=
  match n, t with
  | 0, _ | _ ,tstop => tstop
  | S m, tcons x xs => tcons x (take_n xs m)
 end.                               

Fixpoint take_nth_pref (t : trace) (n : nat) : finpref :=
  match n, t with
  | 0, _ | _ ,tstop => ftbd
  | S m, tcons x xs => fcons x (take_nth_pref xs m)
 end.                               

Lemma nth_pref_pref : forall t n, prefix (take_nth_pref t n) t.
Proof.
  intros t n. generalize dependent t. induction n; intros t; try now auto.
  destruct t; try now auto.
Qed. 

Lemma pref_take_pref : forall m t,
    prefix m t ->
    prefix m (take_n t (length m)).
Proof.
  intros m t. generalize dependent t. induction m; intros t hpref; try now auto.
  + destruct t; try now auto. 
    simpl in *. destruct hpref as [h1 h2]. split; try now auto.
Qed.   

Lemma take_embedding : forall t m,
    prefix m t -> 
    (take_n t (length m)) = embedding m.
Proof.
  intros t m. generalize dependent t. induction m; intros t hpref; try now auto.
  destruct t; try now auto. simpl in *. destruct hpref as [h1 h2].
  subst. now rewrite (IHm t).
Qed. 

Definition ϕ_sem : ϕ_prg -> prop :=
  fun P => 
  (fun t : trace =>
     exists m, t = embedding m /\ psem (snd P) m /\ length m <= (fst P)).

Lemma omega_fact : forall n m, n <= m -> (S n) <= (S m).
Proof. intros n m h. omega. Qed. 

Lemma length_take_n : forall n t,
    length (take_nth_pref t n) <= n.
Proof.
  intros n. induction n; intros t; try now auto.
  destruct t; simpl; try now auto.
  + omega.  
  + apply omega_fact. now apply IHn.
Qed. 
  
Lemma length_smaller : forall P t,
    sem L (snd P) t -> length (take_nth_pref t (fst P)) <= fst P.  
Proof.
  intros P t hsem. now apply length_take_n.
Qed. 

Lemma non_empty_ϕ : forall P, exists t, ϕ_sem P t.
Proof.
  intros P. destruct (non_empty_sem L (snd P)) as [t h].
  exists (embedding (take_nth_pref t (fst P))). unfold ϕ_sem.
  exists (take_nth_pref t (fst P)). repeat (split; try now auto).
  + unfold psem. exists t. split; try now auto. now apply nth_pref_pref.
  + now apply length_smaller.  
Qed.

Lemma fpr_shorter: forall m1 m2, fpr m1 m2 -> length m1 <= length m2.
Proof.
  induction m1; intros m2 hpref; simpl; try omega. 
  + destruct m2; try now auto. inversion hpref; subst.
    simpl. apply omega_fact.  now apply IHm1.
Qed.     
  
(*TODO : move to Tracemdel.v *)         
Lemma prefix_embeding_fpr : forall m1 m2,
    prefix m1 (embedding m2) -> fpr m1 (m2[fstop/ftbd]).
Proof.
  induction m1; intros m2 hpref; try now auto.
  + now destruct m2.
  + destruct m2; try now auto. inversion hpref. subst.
    simpl. split; try now auto.
Qed. 

Lemma leq_trans : forall n1 n2 n3, n1 <= n2 -> n2 <= n3 -> n1 <= n3.
Proof. intros n1 n2 n3 h1 h2. omega. Qed. 

(* intuition there in t in sem longer than m *)
Lemma psem_consequence : forall C P t m,
    ϕ_sem (ϕ_plug P C) t ->
    prefix m t ->  
    length m <= fst C.
Proof.
  intros C P t m [mm [hem [h1 h2]]] hpref. simpl in *.
  rewrite stop_same_lenght in h2. 
  apply (leq_trans (length m) (length(mm[fstop/ftbd])) (fst C)); try now auto.
  apply fpr_shorter; try now auto. 
  rewrite embedding_is_the_same in hem. rewrite hem in hpref.
  apply prefix_embeding_fpr. now rewrite embedding_is_the_same.
Qed. 
    
Definition ϕ := Build_level ϕ_plug
                            ϕ_sem
                            non_empty_ϕ.
                            

(**********************************************************)
(* RSP =/=> RPP                                           *) 
(**********************************************************)

Definition c : prg ϕ -> prg L :=
  fun Pn => snd Pn.

Definition c_RPP (P : prg ϕ) (π : prop) : Prop :=
  rsat P π -> rsat (c P) π.

Lemma C_robustly_safety : forall P S, Safety S -> c_RPP P S. 
Proof. 
  intros P S Hsafety. unfold c_RPP. rewrite contra.
  unfold rsat. repeat rewrite not_forall_ex_not.   
  intros [C hC]. unfold sat in *. rewrite not_forall_ex_not in *.
  destruct hC as [t hh]. rewrite not_imp in hh.
  destruct hh as [h1 h2]. destruct (Hsafety t h2) as [m [hpref hwit]]. 
  exists (length m, C). intros ff. simpl in ff. 
  specialize (hwit (take_n t (length m))). apply hwit.
  now apply pref_take_pref. apply ff. unfold ϕ_sem, ϕ_plug.
  exists m. repeat (split; simpl; try now auto).
  now apply take_embedding. now exists t.
Qed.


Definition an_omega := constant_trace (an_event).  
Definition another_omega := constant_trace (another_event). 

Axiom an_omega_produced : exists P, forall C, sem L (plug L P C) an_omega.
Axiom another_omega_produced : exists P, forall C, sem L (plug L P C) another_omega.

Lemma not_equal: ~ t_eq an_omega another_omega.
Proof.
  rewrite neq_finitely_refutable.
  exists (fcons an_event ftbd), (fcons another_event ftbd). 
  repeat (split; try now auto). 
  intros [f1 f2]. inversion f1. now apply different_events.  
Qed.

Definition my_pi := fun t => fin t \/ t_eq t an_omega.

Lemma my_pi_liveness : Liveness my_pi.
Proof.
  apply all_fin_in_all_liv. unfold my_pi.
  now auto.
Qed.          

Lemma another_omega_not_in_my_pi : ~ my_pi another_omega.
Proof.
 intros [K1 | K2]. 
 + assert (inf another_omega) by now apply inf_constant_trace.
   now auto. 
 + apply t_eq_symm in K2. now apply not_equal. 
Qed. 
   
Lemma cut_lemma : forall C P t, sem ϕ (plug ϕ P C) t -> fin t.
Proof.
  intros C P t H. simpl in*.
  unfold ϕ_sem, ϕ_plug in *. destruct H as [m [hp H]]. rewrite hp.
  now apply embed_fin.
Qed.

Axiom some_ctx_L : ctx L.


Theorem separation_RSP_RLP :
  (forall P π, Safety π -> c_RPP P π) /\
  ~  (forall P π, Liveness π -> c_RPP P π).
Proof.
  split.
  + now apply C_robustly_safety.
  + intros ff. destruct another_omega_produced as [P H]. 
    specialize (ff (42, P) my_pi). unfold c_RPP, rsat, sat in ff.
    simpl in ff. 
    assert (hh :  (forall (C : ctx ϕ) (t : trace), sem ϕ (ϕ_plug (42, P) C) t -> my_pi t)).
    { intros C t H0. simpl in H0. unfold ϕ_sem, ϕ_plug in H0.
      destruct H0 as [m [hm H0]]. left. rewrite hm. 
      now apply embed_fin. } 
    specialize (ff my_pi_liveness hh).  specialize (ff some_ctx_L another_omega).
    assert (sem L (some_ctx_L [P]) another_omega) by now apply (H some_ctx_L).
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

Definition c2 : prg L -> prg ϕ :=
  fun P => (42, P).

Definition c2_RPP (P : prg L) (π : prop) : Prop :=
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

Lemma my_pi2_safety : Safety my_pi2.
Proof.
  unfold Safety, my_pi2. intros t hneq.
  rewrite neq_finitely_refutable in hneq.
  destruct hneq as [m1 [m2 [h1 [h2 h3]]]].
  exists m1. split; try now auto.
  intros tt hh. rewrite neq_finitely_refutable.
  rewrite de_morgan1 in h3. destruct h3 as [k | k].
  + exists m1, m2. repeat (split; try now auto).  
  + admit.
Admitted.


Theorem separation_RLP_RSP :
  (forall P π, Liveness π -> c2_RPP P π) /\
  ~  (forall P π, Safety π -> c2_RPP P π).
Proof.
  split.
  + now apply c2_robustly_liveness.
  + intros ff. destruct an_omega_produced as [P h]. 
    specialize (ff P my_pi2 my_pi2_safety).
    unfold c2_RPP, rsat, sat in ff.
    assert (H : forall (C : ctx L) (t : trace), sem L (C [P]) t -> my_pi2 t).
    { intros C t hsem. admit. (* here we need generalized rewriting! *) }
    specialize (ff H). specialize (ff (0, some_ctx_L) tstop).
    assert  (sem ϕ ((0, some_ctx_L) [c2 P]) tstop).
    simpl. unfold ϕ_sem, ϕ_plug. exists ftbd. 
    repeat (split; try now auto). simpl. exists an_omega.
    split; try now auto. specialize (ff H0).
    unfold my_pi2 in ff. inversion ff. 
Admitted. 


Theorem  separation_RLP_RPP :
   (forall P π, Liveness π -> c2_RPP P π) /\
   ~  (forall P π, c2_RPP P π).
Proof.
  split.
  + now apply c2_robustly_liveness.
  + destruct separation_RLP_RSP as [K1 K2]. now auto.
Qed. 

  