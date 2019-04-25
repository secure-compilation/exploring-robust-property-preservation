Require Import Events.
Require Import TraceModel.
Require Import XPrefix. 
Require Import ClassicalExtras.

 
(** This file defines properties, hyperproperties, relational properties
    and the main subclasses of these *)

(*********************************************************)
(** *Trace Properties                                    *)
(*********************************************************)

Definition prop := trace -> Prop.

Definition Observable (π : prop) : Prop :=
  forall t, π t ->
       (exists m, prefix m t /\
             (forall t', prefix m t' -> π t')).

Definition Safety (π : prop) : Prop :=
  forall t, ~ π t ->
       (exists m, prefix m t /\
            (forall t', prefix m t' -> ~ π t')).


Definition Dense (π : prop) : Prop :=
  forall t, fin t -> π t. 


Definition Liveness (π : prop) : Prop :=
  forall m : finpref, exists t : trace,
      (prefix m t /\ π t).


(* some notes about safety *)

(* Safety a la DG *)
Definition Safety' (π : prop) : Prop:=
  exists π': finpref -> Prop,
  forall t:trace, ~(π t) <-> (exists m, prefix m t /\ π' m).

Lemma safety_safety' : forall π, Safety π <-> Safety' π.
Proof.
   unfold Safety, Safety'. intro π. split; intro H.
  - exists (fun m => forall t, prefix m t -> ~π t).
    intros t. split; intro H'.
    + specialize (H t H'). destruct H as [m [H1 H2]].
      exists m. split. assumption. intros t' H. apply H2. assumption.
    + destruct H' as [m [H1 H2]]. apply H2. assumption.
  - intros t H0. destruct H as [π' H].
    rewrite H in H0. destruct H0 as [m [H1 H2]].
    exists m. split; try now auto.
    intros. rewrite H. now exists m.
Qed.

(* some notes about dense *)

(* In this model a property is Liveness iff it includes all finite traces *)
(* - intuition: can always turn finpref into finite trace by adding fstop *)
Lemma all_fin_in_all_liv :
  forall π, Liveness π <-> Dense π.
Proof.
  unfold Liveness. intros π. split.
  - intros Hl [] Hfin; try contradiction.  
    destruct (Hl (fstop l e)) as [t' [Hpref πt']].
    destruct t'; inversion Hpref; now subst. 
  - intros H []; [exists (tstop l es) | exists (tstop l an_endstate)];
      split; simpl; try now auto; now apply H.
      now apply list_list_prefix_ref.       
Qed.

(* or equivalently if it excludes only infinite traces *)
Lemma not_in_liv_inf :
  forall π, Liveness π <->
       (forall t, ~ π t -> inf t).
Proof.
  intros π. unfold Liveness, inf. split.
  - intros Hl t nt Hfin. apply nt.
    now apply all_fin_in_all_liv.
  - intros H m. exists (embedding an_endstate m). split.
    + now apply embed_pref. 
    + apply NNPP. intros ff. specialize (H (embedding an_endstate m) ff). 
      apply H. now case m. 
Qed.

(* an example: the property excluding one single infinite trace
   is Liveness
 *)
Lemma inf_excluded_is_liv :
  forall ta, inf ta -> Liveness (fun b => b <> ta).
Proof.
  unfold Liveness.
  intros ta Hta m.
  pose proof many_continuations. now eauto.
Qed.


(*********************************************************)
(** *HyperProperties                                      *)
(*********************************************************)


Definition hprop := prop -> Prop.

(* Set of finite prefixes *)
Definition fprop := finpref -> Prop.

(*
   We define observations as finite subsets of finpref
*)
Inductive Observations : (finpref -> Prop) -> Prop :=
| empty :  Observations (fun m : finpref => False)
| finite_union : forall M m, Observations M -> Observations (fun x => M x \/ x = m).

(* extension of prefix relation to sets *)
Definition spref (F : fprop) (T : prop) : Prop :=
  forall x, F x -> (exists t, T t /\ prefix x t).

Lemma spref_monotonic :forall (F : fprop) (T1 T2 : prop),
    spref F T1 ->
    (forall t, T1 t -> T2 t) ->
    spref F T2.
Proof.
   unfold spref. intros F T1 T2 H0 H1 x Fx.
   destruct (H0 x Fx) as [t [Ht pxt]].
   specialize (H1 t Ht). now exists t.
Qed.

Definition spref_x (X : xpref -> Prop) (T : prop) : Prop :=
  forall x, X x -> (exists t, T t /\ xprefix x t). 


(** *SubsetClosed Hyperproperties *)

Definition subset (π1 π2 : prop) : Prop :=
  forall t, π1 t -> π2 t.

Infix "⊆" := subset (at level 50).

Lemma subset_trans : forall X Y Z,
    X ⊆ Y -> Y ⊆ Z -> X ⊆ Z.
Proof.
  intros X Y Z H1 H2. unfold subset in *.
  intros t xt. now apply (H2 t (H1 t xt)).
Qed.

Definition SSC (H : hprop) : Prop :=
  forall h, H h ->
       (forall k, k ⊆ h -> H k).

Definition lifting (h : prop) : hprop :=
  fun π => π ⊆ h.


Definition class_lift (H : prop -> Prop) : hprop -> Prop :=
  fun (h : hprop) => exists π, H π /\ h = lifting π.


(*  every SSC Hyperproperty is the union of
    the lifting of its elements
 *)
Lemma SSC_equiv :
  forall H π, SSC H ->
   H π <-> (fun k => exists h, H h /\ (lifting h) k) π. (* U { [h] | h ∈ H } *)
Proof.
  intros H π sscH. split.
  - intros HH. exists π. split.
    + assumption.
    + unfold lifting, subset. auto.
  - intros [h [Kh lifth]]. unfold lifting in lifth.
    now apply (sscH h Kh π lifth).
Qed.


(* The union of the lifting of
   properties is a SSC Hyperproperty
 *)

Lemma Union_Lift_SSC : forall H,
    SSC (fun k => exists h, H h /\ (lifting h) k).
Proof.
 unfold SSC. intros H h [k [Hk liftkh]] π subh.
 exists k. split.
 - assumption.
 - unfold lifting in *. now apply (subset_trans π h k).
Qed.

(* For every Hyperproperty H,
   H is SSC iff eixsts a family of properties H' (i.e. another Hyperproperty)
   s.t. the "closure of H'" is equal to H
*)

Theorem SSC_iff : forall H,
    SSC H <->
     (exists H',
      (forall π, (fun k => exists h, H' h /\ (lifting h) k) π <-> H π)).
Proof.
  intros H. split.
  - intros ssc. exists H.
    intros π. now rewrite <- (SSC_equiv H π ssc).
  - unfold SSC. intros [H' HH] h Hh k subkh.
    destruct (HH k) as [K0 K1].
    destruct (HH h) as [H0 H1].
    apply K0. destruct (H1 Hh) as [π [X0 X1]].
    clear H1 H0. exists π. split.
    + assumption.
    + unfold lifting in *. now apply (subset_trans k h π).
Qed.

(* definition by "Verifying Bounded Subset-Closed Hyperproperties" 
   - Mastroeni, Pasqua *)
Definition twoSC (H : hprop) : Prop :=
  forall b, ~ (H b) <-> (exists t1 t2, (b t1 /\ b t2 /\ ~ H (fun t => t = t1 \/ t = t2))).

Lemma twoSC_SSC (H: hprop) : twoSC H -> SSC H.
Proof.
  intros twosc b H_b b' b'_leq_b.
  apply NNPP. intros not_H_b'.
  rewrite (twosc b') in not_H_b'. destruct not_H_b' as [t1 [t2 [b_t1 [b_t2 H_t1_t2]]]].
  rewrite dne in H_b. apply H_b.
  rewrite (twosc _). exists t1, t2. split; auto.
Qed. 

(* 2SC Hyperproperties *)

(* CA : according to the old definition 

         H ∈ twoSC iff ∃ t1 t2. ∀ b. ~ (H b) <->  (b t1 /\ b t2).

         hence

         H ∈ k-SC iff 
         ∃ t1 .. tk, H = lifting (true \ t1) ∪ .. ∪ lifting (true \ tk)

   notice that

   (1) H ∈ 2-SC -> H ∈ k-SC ∀ k >= 2   (just take t3 = .. = tk = t2)
   
   (2) H ∈ 2-SC -> H ∈ SC 
       by a previous characterization of SC hyperproperties.

   ------------------------------------------------------------------------------

   for k -> ∞ 

    H ∈ lim_{k -> ∞ } k -SC iff
    H = ∪_{t : trace} lifting (true \ t) = prop \ {t | t : trace}

   Consequences : 
   ---------------

   (i)   such a limit is not the class SSC (and it contains only one hyperproperty)

   (ii)  H ∈ 2-SC does not imply H ∈ lim_{k -> ∞ } k -SC   

         e.g. lifting (true \ t) for a fixed t is in 2-SC (as ∃ t, t ..)
              
               but it is different from 
               prop \ {t | t : trace} (the only inhabitant of lim_{k -> ∞ } k -SC)


 CA: anycase nothing changes in the diagram, 
     see theorem  R2SCHP_R2HSP 
     
 *)


(** *HyperSafety *)

Definition HSafe (H : hprop) : Prop :=
  forall T, ~ H T -> (exists M, Observations M /\ spref M T /\
                     (forall T', spref M T' -> ~ H T')).

(* CA: TODO try to prove the viceversa *)
Lemma safety_lifting : forall π, Safety π -> HSafe (lifting π).
Proof.
  intros π. unfold Safety, HSafe.
  - intros h T h0. assert (K : (forall b, ~ T b) \/ (exists b, T b /\ ~ π b)).
    { assert (foo : (forall b, ~ T b) \/ ~(forall b,  ~T b)) by now apply classic.
      unfold lifting, "⊆" in h0. rewrite not_forall_ex_not in h0.
      destruct h0 as [b h0]. rewrite not_imp in h0. right. now exists b.
    }
    destruct K as [K | [b [K1 K2]]].
    + exfalso. apply h0. unfold lifting, "⊆". intros t ff.
      exfalso. apply (K t ff).
    + destruct (h b K2) as [m [h1 h2]].
      exists (fun m' => False \/  m' = m). split.
      ++ repeat constructor.
      ++ split. unfold spref, "⊆". intros x [hx | hx]; inversion hx.
         now  exists b.
         intros T' h' ff. unfold spref, "⊆" in h'.
         destruct (h' m) as [t [ht hmt]]. now right.
         unfold lifting, "⊆" in ff. now apply ((h2 t hmt) (ff t ht)).
Qed.

(* 2-Hypersafety *)
Definition H2Safe (H : hprop) : Prop :=
  forall (b : prop), ~ (H b) ->
                (exists (m1 m2 : finpref),
                    spref (fun m => m = m1 \/ m = m2) b /\
                    forall b', spref (fun m => m = m1 \/ m = m2) b' -> ~(H b')).

Lemma twoSC_H2Safe (H : hprop) : H2Safe H -> twoSC H.
Proof.
  intros hsafe_H b. split.
  + intros not_H_b. destruct (hsafe_H b not_H_b) as [m1 [m2 [spref_b wit]]].
    destruct (spref_b m1) as [t1 [b_t1 m1_t1]]; auto.     
    destruct (spref_b m2) as [t2 [b_t2 m2_t2]]; auto. 
    exists t1, t2. repeat (split; auto). apply wit.
    intros m [M1 | M2]; subst; [exists t1 | exists t2]; auto. 
  + intros [t1 [t2 [b_t1 [b_t2 not_H]]]].
    destruct (hsafe_H _ not_H) as [m1 [m2 [spref_b wit]]].
    apply wit.
    intros m [M1 | M2]; subst.
    ++ destruct (spref_b m1) as [t [b_t pref_t]]; auto.
       destruct b_t; subst; [now exists t1 | now exists t2].
    ++ destruct (spref_b m2) as [t [b_t pref_t]]; auto.
       destruct b_t; subst; [now exists t1 | now exists t2].
Qed.    
    
(** *HyperLiveness *)
Definition HLiv (H : hprop) : Prop :=
  forall M, Observations M ->
       (exists T, spref M T /\ H T).


Definition Embedding (M : finpref -> Prop) : prop :=
  fun t => exists m es, M m /\ t = embedding es m.

Lemma infinite_trace_not_in_embed : forall M, ~ (Embedding M) (tstream (constant_stream an_event)).
Proof.
  intros M hf. inversion hf. destruct H as [es [h1 h2]].
  unfold embedding in h2. destruct x; inversion h2.  
Qed.


(*********************************************************)
(** *Relational (Hyper)Properties                        *)
(*********************************************************)

Definition rel_prop := trace -> trace -> Prop.
Definition rel_hprop:= prop  -> prop -> Prop.

Definition safety2 (r : rel_prop) :=
  forall (t1 t2 : trace),  ~ (r t1 t2) ->
    exists (m1 m2 : finpref),
      prefix m1 t1 /\ prefix m2 t2 /\
      (forall (t1' t2' : trace), prefix m1 t1' -> prefix m2 t2' -> ~(r t1' t2')).


Definition ssc2 (r : rel_hprop) :=
  forall b1 b2 b1' b2', r b1 b2 -> subset b1' b1 -> subset b2' b2 -> r b1' b2'.


Definition xafety2 r := forall (t1 t2 : trace),
  ~ (r t1 t2) ->
  exists (m1 m2 : xpref), xprefix m1 t1 /\ xprefix m2 t2 /\
    (forall (t1' t2' : trace), xprefix m1 t1' -> xprefix m2 t2' -> ~(r t1' t2')).