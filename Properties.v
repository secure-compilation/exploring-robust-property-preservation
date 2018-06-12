Require Import Events.
Require Import TraceModel. 
Require Import ClassicalExtras.

(* CA: in this file all and only defn of prop, Hprop, relation on prop
       and main classes of these *)
(*******************************************************)

Definition prop := trace -> Prop.

Definition Observable (π : prop) : Prop :=
  forall t, π t ->
       (exists m, prefix m t /\
             (forall t', prefix m t' -> π t')).

Definition Safety (π : prop) : Prop :=
  forall t, ~ π t ->
       (exists m, prefix m t /\
            (forall t', prefix m t' -> ~ π t')).

Definition Liveness (π : prop) : Prop :=
  forall m : finpref, exists t : trace,
      (prefix m t /\ π t).

(*******************************************************)

(* some notes about safety *)

(* Safety a la Deepak *)
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

Lemma safety_bad_finite_prefix : forall π, Safety π ->
  forall t:trace, ~(π t) -> (exists m:finpref, prefix m t /\ ~(π (embedding m))).
Proof.
  unfold Safety. intros π H t H0.
  specialize (H t H0). destruct H as [m [H1 H2]].
  exists m. split. assumption.
  apply H2. now apply embed_pref.
Qed.

(* some notes about liveness *)

(* In this model a property is Liveness iff it includes all finite traces *)
(* - intuition: can always turn finpref into finite trace by adding fstop *)
Lemma all_fin_in_all_liv :
  forall π, Liveness π <->
   (forall t, fin t -> π t).
Proof.
  unfold Liveness. intros π. split.
  - intros Hl t Hfin.
    destruct (single_cont_consequence _ Hfin) as [m H].
    destruct (Hl m) as [t' [H1 H2]]. erewrite H; eauto.
  - intros H m. exists (embedding m). split.
    + now apply embed_pref.
    + apply H. now apply embed_fin.
Qed.

(* or equivalently if it excludes only infinite traces *)
Lemma not_in_liv_inf :
  forall π, Liveness π <->
       (forall t, ~ π t -> inf t).
Proof.
  intros π. unfold Liveness, inf. split.
  - intros Hl t nt Hfin. apply nt.
    now apply all_fin_in_all_liv.
  - intros H m. exists (embedding m). split.
    + now apply embed_pref.
    + apply NNPP. intros ff. specialize (H (embedding m) ff).
      apply H. now apply embed_fin.
Qed.

(* an example: the property excluding one single infinite trace
   is Liveness
 *)
Lemma inf_excluded_is_liv :
  forall ta, inf ta -> Liveness (fun b => b <> ta).
Proof.
  unfold Liveness. intros ta m. pose proof many_continuations. now eauto.
Qed.


(*******************************************************)

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


(*********************************************************)
(** SubSetClosed                                         *)
(*********************************************************)

Definition subset (π1 π2 : prop) : Prop :=
  forall t, π1 t -> π2 t.

Notation "X << Y" := (subset X Y) ( at level 50).

Lemma subset_trans : forall X Y Z,
    X << Y -> Y << Z -> X << Z.
Proof.
  intros X Y Z H1 H2. unfold subset in *.  
  intros t xt. now apply (H2 t (H1 t xt)).
Qed.
  
Definition SSC (H : hprop) : Prop :=
  forall h, H h ->
       (forall k, k << h -> H k).

Definition lifting (h : prop) : hprop :=
  fun π => π << h.

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

(** *HyperSafety *)

(* CA: TODO try to prove the viceversa *)
Definition HSafe (H : hprop) : Prop :=
  forall T, ~ H T -> (exists M, Observations M /\ spref M T /\
                     (forall T', spref M T' -> ~ H T')).

Lemma safety_lifting : forall π, Safety π -> HSafe (lifting π).
Proof.
  intros π. unfold Safety, HSafe.
  - intros h T h0. assert (K : (forall b, ~ T b) \/ (exists b, T b /\ ~ π b)).
    { assert (foo : (forall b, ~ T b) \/ ~(forall b,  ~T b)) by now apply classic.
      unfold lifting, "<<" in h0. rewrite not_forall_ex_not in h0.
      destruct h0 as [b h0]. rewrite not_imp in h0. right. now exists b.
    }
    destruct K as [K | [b [K1 K2]]].
    + exfalso. apply h0. unfold lifting, "<<". intros t ff.
      exfalso. apply (K t ff).
    + destruct (h b K2) as [m [h1 h2]]. 
      exists (fun m' => False \/  m' = m). split.
      ++ repeat constructor.
      ++ split. unfold spref, "<<". intros x [hx | hx]; inversion hx.
         now  exists b.
         intros T' h' ff. unfold spref, "<<" in h'.
         destruct (h' m) as [t [ht hmt]]. now right.
         unfold lifting, "<<" in ff. now apply ((h2 t hmt) (ff t ht)).
Qed.


(** *HyperLiveness *)
Definition HLiv (H : hprop) : Prop :=
  forall M, Observations M ->
       (exists T, spref M T /\ H T).

(*******************************************************)

Definition rel_prop := trace -> trace -> Prop.

