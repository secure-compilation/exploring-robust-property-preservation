Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import ClassicalExtras.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalFacts.

Axiom Prop_Ext : prop_extensionality.

Inductive filter (P : event -> Prop) : trace -> trace -> Prop :=
| filter_tstop : filter P tstop tstop
| filter_tsilent : filter P tsilent tsilent
| filter_tcons_true : forall (e : event) (t t' : trace),
    filter P t t' ->
    P e ->
    filter P (tcons e t) (tcons e t')
| filter_tcons_false : forall (e : event) (t t' : trace),
    filter P t t' ->
    ~ P e ->
    filter P (tcons e t) t'
.
Hint Constructors filter.

Axiom pub : event -> Prop.
Axiom pubb : event -> bool.
Axiom pub_pubb : forall (e : event), pub e <-> pubb e = true.

Axiom input : event -> Prop.
Axiom inputb : event -> bool.
Axiom input_inputb : forall (e : event), input e <-> inputb e = true.

Definition pub_input : event -> Prop :=
  fun i => pub i /\ input i.
Definition pub_inputb : event -> bool :=
  fun i => andb (pubb i) (inputb i).
Lemma pub_input_pub_inputb : forall (e : event),
    pub_input e <-> pub_inputb e = true.
Proof.
  intros e; split; unfold pub_input; unfold pub_inputb.
  - intros H.
    destruct H as [H1 H2].
    apply pub_pubb in H1.
    apply input_inputb in H2.
    now rewrite H1; rewrite H2.
  - intros H.
    apply andb_prop in H.
    destruct H; split. now apply pub_pubb. now apply input_inputb.
Qed.

Definition stopped := fin.

Definition NI_fun : hprop :=
  fun b => forall (p1 p2 : pref),
      b (tapp (fstop p1) tstop) -> b (tapp (fstop p2) tstop) ->
      (List.filter pub_inputb p1) = (List.filter pub_inputb p2) ->
      (List.filter pubb p1) = (List.filter pubb p2).

Theorem HS_NI_fun : HSafe NI_fun.
Proof.
  unfold HSafe, NI_fun.
  intros b HnNI.
  rewrite not_forall_ex_not in HnNI.
  destruct HnNI as [p1 HnNI].
  rewrite not_forall_ex_not in HnNI.
  destruct HnNI as [p2 HnNI].
  rewrite not_imp in HnNI; destruct HnNI as [Hbt1 HnNI].
  rewrite not_imp in HnNI; destruct HnNI as [Hbt2 HnNI].
  rewrite not_imp in HnNI. destruct HnNI as [H1 H2].
  exists (fun m => m = (fstop p1) \/ m = (fstop p2)).
  repeat split.
  - constructor.
    assert ((fun x : finpref => x = fstop p1) = (fun x : finpref => False \/ x = fstop p1)).
    { clear.
      apply functional_extensionality.
      intros m.
      assert (forall P: Prop, (False \/ P) <-> P).
      { intros; split; intros.
        destruct H; now auto.
        right. apply H.
      }
      specialize (H (m = fstop p1)).
      apply Prop_Ext. now symmetry.
    }
    rewrite H. constructor. constructor.
  - unfold spref.
    intros m Hm.
    destruct Hm as [Hm | Hm]; subst.
    exists (tapp (fstop p1) tstop); split; auto. apply tapp_pref.
    exists (tapp (fstop p2) tstop); split; auto. apply tapp_pref.
  - intros b' Hb'.
    unfold spref in Hb'.
    pose proof Hb' as Hb''.
    specialize (Hb' (fstop p1)).
    assert (fstop p1 = fstop p1 \/ fstop p1 = fstop p2) by now left.
    specialize (Hb' H). destruct Hb' as [t1 [Ht1 Ht1']]. clear H.
    specialize (Hb'' (fstop p2)).
    assert (fstop p2 = fstop p1 \/ fstop p2 = fstop p2) by now right.
    specialize (Hb'' H). destruct Hb'' as [t2 [Ht2 Ht2']]. clear H.
    intros Hn.
    assert (forall p t, prefix (fstop p) t -> t = tapp (fstop p) tstop).
    { clear. induction p; destruct t; intros H; try now auto.
      simpl in *. destruct H; subst. specialize (IHp t H0). now subst. }
    assert (H1' : b' (tapp (fstop p1) tstop)) by now specialize (H p1 t1 Ht1'); subst.
    assert (H2' : b' (tapp (fstop p2) tstop)) by now specialize (H p2 t2 Ht2'); subst.
    specialize (Hn p1 p2 H1' H2' H1). now contradiction.
Qed.


(* First definition of noninterference, with filter *)
Definition NI : hprop :=
  fun b => forall (t1 t2 : trace), b t1 -> b t2 ->
                           (fin t1 /\ fin t2 /\
                            exists t', filter pub_input t1 t' /\ filter pub_input t2 t') ->
                           exists t', filter pub t1 t' /\ filter pub t2 t'.

Lemma filter_filter_rel : forall (P : event -> Prop) (Pf : event -> bool) (H: forall e, P e <-> Pf e = true)
                            (p1 p2 : pref), 
    (exists t', filter P (tapp (fstop p1) tstop) t' /\ filter P (tapp (fstop p2) tstop) t')
    <-> (List.filter Pf p1 = List.filter Pf p2).
Proof.
  intros P Pf H p1 p2.
  split.
  - generalize dependent p2.
    induction p1; induction p2; try now auto.
    + intros [t' [Ht'1 Ht'2]].
      inversion Ht'2; subst; try now auto.
      assert (Pf a = false).
      { specialize (H a). destruct (Pf a). exfalso. apply H4. apply H. reflexivity.
        reflexivity. }
      simpl; rewrite H0.
      assert (exists t' : trace, filter P (tapp (fstop nil) tstop) t' /\
                            filter P (tapp (fstop p2) tstop) t').
      { exists t'. split. assumption.
        inversion Ht'2; subst; now auto. }
      now specialize (IHp2 H1).
    + intros [t' [Ht'1 Ht'2]].
      inversion Ht'1; subst; try now auto.
      assert (Pf a = false).
      { specialize (H a). destruct (Pf a). exfalso. apply H4. apply H. reflexivity.
        reflexivity. }
      simpl; rewrite H0. specialize (IHp1 nil).
      assert (exists t' : trace,
                 filter P (tapp (fstop p1) tstop) t' /\ filter P (tapp (fstop nil) tstop) t').
      { exists t'. split; assumption. }
      now specialize (IHp1 H1).
    + intros [t' [Ht'1 Ht'2]].
      inversion Ht'1; inversion Ht'2; subst.
      * inversion H8; subst. apply H in H4. simpl; rewrite H4; simpl.
        specialize (IHp1 p2).
        assert (exists t' : trace, filter P (tapp (fstop p1) tstop) t' /\
                              filter P (tapp (fstop p2) tstop) t').
        { exists t'0. split; assumption. }
        specialize (IHp1 H0). now rewrite IHp1.
      * apply H in H4.
        assert (Pf a0 = false).
        { specialize (H a0). destruct (Pf a0). exfalso. apply H9. apply H. reflexivity.
          reflexivity. }
        simpl; rewrite H4, H0.
        assert (exists t' : trace, filter P (tapp (fstop (a :: p1)%list) tstop) t' /\
                              filter P (tapp (fstop p2) tstop) t').
        { exists (tcons a t'0). split; assumption. }
        specialize (IHp2 H1). rewrite <- IHp2. simpl. rewrite H4. reflexivity.
      * apply H in H9.
        assert (Pf a = false).
        { specialize (H a). destruct (Pf a). exfalso. apply H4. apply H. reflexivity.
          reflexivity. }
        simpl; rewrite H9, H0.
        specialize (IHp1 (cons a0 p2)).
        assert (exists t' : trace, filter P (tapp (fstop p1) tstop) t' /\
                              filter P (tapp (fstop (a0 :: p2)%list) tstop) t').
        { exists (tcons a0 t'1). split; assumption. }
        specialize (IHp1 H1). rewrite IHp1. simpl. rewrite H9. reflexivity.
      * assert (Pf a0 = false).
        { specialize (H a0). destruct (Pf a0). exfalso. apply H9. apply H. reflexivity.
          reflexivity. }
        assert (Pf a = false).
        { specialize (H a). destruct (Pf a). exfalso. apply H4. apply H. reflexivity.
          reflexivity. }
        simpl. rewrite H0, H1. apply (IHp1 p2).
        exists t'. now split.
  - intros H'.
    exists (tapp (fstop (List.filter Pf p1)) tstop).
    generalize dependent p2.
    induction p1; induction p2; intros H'; try now auto.
    + split; try now auto.
      simpl in *.
      destruct (Pf a) eqn: Heq; try now auto.
      specialize (IHp2 H'). destruct IHp2. constructor.
      assumption.
      intros Hn. apply H in Hn. rewrite Heq in Hn. inversion Hn.
    + simpl in *.
      destruct (Pf a) eqn:Heq; try now auto.
      specialize (IHp1 nil H'). destruct IHp1.
      split. constructor. assumption. intros Hn; apply H in Hn; rewrite Hn in Heq; inversion Heq.
      simpl in H1; assumption.
    + simpl in *.
      destruct (Pf a) eqn:Heq; destruct (Pf a0) eqn:Heq'; try now auto.
      * inversion H'; subst.
        specialize (IHp1 p2 H2). destruct IHp1.
        split; constructor; try now apply H. assumption. assumption.
      * specialize (IHp2 H'). destruct IHp2.
        split; constructor; try assumption. destruct p2; try now auto.
        simpl in *. inversion H0; subst; try now auto. apply H in Heq. contradiction.
        now apply H in Heq.
        intros Hn; apply H in Hn. rewrite Hn in Heq'; inversion Heq'.
      * assert (List.filter Pf p1 = List.filter Pf (a0 :: p2)).
        { simpl. rewrite Heq'. assumption. }
        specialize (IHp1 (cons a0 p2) H0). destruct IHp1.
        split. constructor. assumption. intros Hn; apply H in Hn; rewrite Hn in Heq; inversion Heq.
        simpl in H2. assumption.
      * specialize (IHp2 H').
        destruct IHp2.
        split. assumption. constructor. assumption.
        intros Hn; apply H in Hn; rewrite Hn in Heq'; inversion Heq'.
Qed.


Theorem NI_NI_fun : forall (b : prop), NI b <-> NI_fun b.
Proof.
  unfold NI, NI_fun.
  intros b. split.
  - intros H p1 p2 Hp1 Hp2 Hfilter.
    specialize (H (tapp (fstop p1) tstop) (tapp (fstop p2) tstop) Hp1 Hp2).
    assert .
  - admit.
Admitted.