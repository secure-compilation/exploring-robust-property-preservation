(* Add LoadPath ".". *)

Inductive HExp :=
  HNat : nat -> HExp
| HBool : bool -> HExp
| HPlus : HExp -> HExp -> HExp
| HTimes : HExp -> HExp -> HExp
| HIte : HExp -> HExp -> HExp -> HExp
| HLe : HExp -> HExp -> HExp
| HInput : HExp.

Inductive LExp :=
  LNat : nat -> LExp
| LPlus : LExp -> LExp -> LExp
| LTimes : LExp -> LExp -> LExp
| LIte : LExp -> LExp -> LExp -> LExp -> LExp
| LInput.

Fixpoint compile (he : HExp) : LExp :=
  match he with
    HNat n => LNat n
  | HBool true => LNat 1
  | HBool false => LNat 0
  | HPlus he1 he2 => LPlus (compile he1) (compile he2)
  | HTimes he1 he2 => LTimes (compile he1) (compile he2)
  | HLe he1 he2 => LIte (compile he1) (compile he2) (LNat 1) (LNat 0)
  | HIte he1 he2 he3 => LIte (compile he1) (LNat 0) (compile he3) (compile he2)
  | HInput => LInput
  end.

Require Import List.

Inductive HResult :=
| HRBool : bool -> HResult
| HRNat : nat -> HResult
| HRError : HResult.

Definition HTrace := (list nat * HResult)%type.

Inductive LResult :=
| LRNat : nat -> LResult.

Definition LTrace := (list nat * LResult)%type.

Import ListNotations.

Inductive hsem : HExp -> HTrace -> Prop :=
| HSNat : forall n,
    hsem (HNat n) (nil, HRNat n)
| HSBool : forall b,
    hsem (HBool b) (nil, HRBool b)

| HSPlusSuccess : forall he1 hl1 n1,
    forall he2 hl2 n2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRNat n2) ->
      hsem (HPlus he1 he2) (app hl1 hl2, HRNat (n1 + n2))
| HSPlusLeftBool : forall he1 hl1 b1 he2,
    hsem he1 (hl1, HRBool b1) ->
    hsem (HPlus he1 he2) (hl1, HRError)
| HSPlusLeftError : forall he1 hl1 he2,
    hsem he1 (hl1, HRError) ->
    hsem (HPlus he1 he2) (hl1, HRError)
| HSPlusRightBool : forall he1 hl1 n1,
    forall he2 hl2 b2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRBool b2) ->
      hsem (HPlus he1 he2) (app hl1 hl2, HRError)
| HSPlusRightError : forall he1 hl1 n1,
    forall he2 hl2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRError) ->
      hsem (HPlus he1 he2) (app hl1 hl2, HRError)

| HSTimesSuccess : forall he1 hl1 n1,
    forall he2 hl2 n2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRNat n2) ->
      hsem (HTimes he1 he2) (app hl1 hl2, HRNat (n1 * n2))
| HSTimesLeftBool : forall he1 hl1 b1 he2,
    hsem he1 (hl1, HRBool b1) ->
    hsem (HTimes he1 he2) (hl1, HRError)
| HSTimesLeftError : forall he1 hl1 he2,
    hsem he1 (hl1, HRError) ->
    hsem (HTimes he1 he2) (hl1, HRError)
| HSTimesRightBool : forall he1 hl1 n1,
    forall he2 hl2 b2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRBool b2) ->
      hsem (HTimes he1 he2) (app hl1 hl2, HRError)
| HSTimesRightError : forall he1 hl1 n1,
    forall he2 hl2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRError) ->
      hsem (HTimes he1 he2) (app hl1 hl2, HRError)
           
| HSIteLeft : forall he1 he2 he3 hl1 hl2 r2,
    hsem he1 (hl1, HRBool true) ->
    hsem he2 (hl2, r2) ->
    hsem (HIte he1 he2 he3) (app hl1 hl2, r2)
| HSIteRight : forall he1 he2 he3 hl1 hl3 r3,
    hsem he1 (hl1, HRBool false) ->
    hsem he3 (hl3, r3) ->
    hsem (HIte he1 he2 he3) (app hl1 hl3, r3)
| HSIteNat : forall he1 he2 he3 hl1 n1,
    hsem he1 (hl1, HRNat n1) ->
    hsem (HIte he1 he2 he3) (hl1, HRError)
| HSIteError : forall he1 he2 he3 hl1,
    hsem he1 (hl1, HRError) ->
    hsem (HIte he1 he2 he3) (hl1, HRError)

| HSLeSuccess : forall he1 hl1 n1,
    forall he2 hl2 n2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRNat n2) ->
      hsem (HLe he1 he2) (app hl1 hl2, HRBool (Nat.leb n1 n2))
| HSLeLeftBool : forall he1 hl1 b1 he2,
    hsem he1 (hl1, HRBool b1) ->
    hsem (HLe he1 he2) (hl1, HRError)
| HSLeLeftError : forall he1 hl1 he2,
    hsem he1 (hl1, HRError) ->
    hsem (HLe he1 he2) (hl1, HRError)
| HSLeRightBool : forall he1 hl1 n1,
    forall he2 hl2 b2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRBool b2) ->
      hsem (HLe he1 he2) (app hl1 hl2, HRError)
| HSLeRightError : forall he1 hl1 n1,
    forall he2 hl2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRError) ->
      hsem (HLe he1 he2) (app hl1 hl2, HRError)
| HSInput : forall n,
    hsem HInput ([n], HRNat n).

Inductive lsem : LExp -> LTrace -> Prop :=
| LSNat : forall n,
    lsem (LNat n) (nil, LRNat n)

| LSPlusSuccess : forall le1 ll1 n1,
    forall le2 ll2 n2,
      lsem le1 (ll1, LRNat n1) ->
      lsem le2 (ll2, LRNat n2) ->
      lsem (LPlus le1 le2) (app ll1 ll2, LRNat (n1 + n2))

| LSTimesSuccess : forall le1 ll1 n1,
    forall le2 ll2 n2,
      lsem le1 (ll1, LRNat n1) ->
      lsem le2 (ll2, LRNat n2) ->
      lsem (LTimes le1 le2) (app ll1 ll2, LRNat (n1 * n2))
| LSIteLeft : forall le1 le2 le3 le4 ll1 ll2 ll3 n1 n2 n3,
    lsem le1 (ll1, LRNat n1) ->
    lsem le2 (ll2, LRNat n2) ->
    le n1 n2 ->
    lsem le3 (ll3, LRNat n3) ->
    lsem (LIte le1 le2 le3 le4) (app ll1 (app ll2 ll3), LRNat n3)
| LSIteRight : forall le1 le2 le3 le4 ll1 ll2 ll4 n1 n2 n4,
    lsem le1 (ll1, LRNat n1) ->
    lsem le2 (ll2, LRNat n2) ->
    not (le n1 n2) ->
    lsem le4 (ll4, LRNat n4) ->
    lsem (LIte le1 le2 le3 le4) (app ll1 (app ll2 ll4), LRNat n4)
| LSInput : forall n,
    lsem LInput ([n], LRNat n).

Definition tilde (ht : HTrace) (lt : LTrace) : Prop :=
  match ht, lt with
  | (l1, HRNat n1), (l2, LRNat n2) => l1 = l2 /\ n1 = n2
  | (l1, HRBool true), (l2, LRNat 1)
  | (l1, HRBool false), (l2, LRNat 0) => l1 = l2
  | _, _ => False
  end.

(* (* another way this could be defined *) *)
(* Definition tilde' (ht:HTrace) (lt:LTrace) : Prop := *)
(*   match ht, lt with *)
(*   | (l1, HRNat n1), (l2, LRNat n2) => l1 = l2 /\ n1 = n2 *)
(*   | (l1, HRBool true), (l2, LRNat 1) *)
(*   | (l1, HRBool false), (l2, LRNat 0) => l1 = l2 *)
(*   | _, _ => False *)
(*   end. *)

Inductive type :=
  TNat
| TBool.

Inductive typing : HExp -> type -> Prop :=
| type_nat : forall n, typing (HNat n) TNat
| type_bool : forall b, typing (HBool b) TBool
| type_plus : forall he1 he2,
    typing he1 TNat ->
    typing he2 TNat ->
    typing (HPlus he1 he2) TNat
| type_times : forall he1 he2,
    typing he1 TNat ->
    typing he2 TNat ->
    typing (HTimes he1 he2) TNat
| type_hite : forall he1 he2 he3 t,
    typing he1 TBool ->
    typing he2 t ->
    typing he3 t ->
    typing (HIte he1 he2 he3) t
| type_hle : forall he1 he2,
    typing he1 TNat ->
    typing he2 TNat ->
    typing (HLe he1 he2) TBool
| type_hinput :
    typing HInput TNat.

Theorem type_correct :
  forall he : HExp,
  forall t : type,
    typing he t ->
    forall l hr,
      hsem he (l, hr) ->
      (t = TNat -> exists n, hr = HRNat n) /\
      (t = TBool -> exists b, hr = HRBool b).
Proof.
  induction he; intros; split; intros; subst.
  - exists n. inversion H0. subst. reflexivity.
  - inversion H.
  - inversion H.
  - exists b. inversion H0. subst. reflexivity.
  - (* HPlus *) inversion H0. subst.
    + inversion H. subst.
      specialize (IHhe1 TNat H3 hl1 (HRNat n1)).
      specialize (IHhe2 TNat H5 hl2 (HRNat n2)).
      destruct IHhe1 as [ IHhe1' IHhe1'' ].
      destruct IHhe2 as [ IHhe2' IHhe2'' ].
      assumption.
      assumption.
      exists (plus n1 n2).
      simpl. reflexivity.
    + inversion H. subst.
      specialize (IHhe1 TNat H8 l (HRBool b1) H2).
      destruct IHhe1.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHhe1 TNat H8 l HRError H2).
      destruct IHhe1.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHhe2 TNat H10 hl2 (HRBool b2) H6).
      destruct IHhe2.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHhe2 TNat H10 hl2 HRError H6).
      destruct IHhe2.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
  - (* HPlus Bool *) inversion H.
  - (* HTimes *) inversion H0. subst.
    + inversion H. subst.
      specialize (IHhe1 TNat H3 hl1 (HRNat n1)).
      specialize (IHhe2 TNat H5 hl2 (HRNat n2)).
      destruct IHhe1 as [ IHhe1' IHhe1'' ].
      destruct IHhe2 as [ IHhe2' IHhe2'' ].
      assumption.
      assumption.
      exists (mult n1 n2).
      simpl. reflexivity.
    + inversion H. subst.
      specialize (IHhe1 TNat H8 l (HRBool b1) H2).
      destruct IHhe1.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHhe1 TNat H8 l HRError H2).
      destruct IHhe1.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHhe2 TNat H10 hl2 (HRBool b2) H6).
      destruct IHhe2.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHhe2 TNat H10 hl2 HRError H6).
      destruct IHhe2.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
  - inversion H.
  - admit.
  (* - (* ite return TNat *) inversion H. subst. *)
  (*   specialize (IHhe1 TBool H3). *)
  (*   specialize (IHhe2 TNat H5). *)
  (*   specialize (IHhe3 TNat H6). *)
  (*   destruct IHhe1 as [ IHhe1' IHhe1'' ]. *)
  (*   destruct IHhe2 as [ IHhe2' IHhe2'' ]. *)
  (*   destruct IHhe3 as [ IHhe3' IHhe3'' ]. *)
  (*   clear IHhe1'. *)
  (*   clear IHhe2''. *)
  (*   clear IHhe3''. *)
  (*   specialize (IHhe1'' eq_refl). *)
  (*   specialize (IHhe2' eq_refl). *)
  (*   specialize (IHhe3' eq_refl). *)
  (*   inversion IHhe1'' as [ b Hb ]. *)
  (*   destruct b. *)
  (*   + destruct IHhe2' as [ n2 ]. *)
  (*     exists n2. *)
  (*     simpl. rewrite Hb. assumption. *)
  (*   + destruct IHhe3' as [ n3 ]. *)
  (*     exists n3. *)
  (*     simpl. rewrite Hb. *)
  (*     assumption. *)
  - (* ite returning TBool *)
    admit.
    (* inversion H. subst. *)
    (* specialize (IHhe1 TBool H3). *)
    (* specialize (IHhe2 TBool H5). *)
    (* specialize (IHhe3 TBool H6). *)
    (* destruct IHhe1 as [ IHhe1' IHhe1'' ]. *)
    (* destruct IHhe2 as [ IHhe2' IHhe2'' ]. *)
    (* destruct IHhe3 as [ IHhe3' IHhe3'' ]. *)
    (* clear IHhe1'. *)
    (* clear IHhe2'. *)
    (* clear IHhe3'. *)
    (* specialize (IHhe1'' eq_refl). *)
    (* specialize (IHhe2'' eq_refl). *)
    (* specialize (IHhe3'' eq_refl). *)
    (* inversion IHhe1'' as [ b Hb ]. *)
    (* destruct b. *)
    (* + destruct IHhe2'' as [ b2 ]. *)
    (*   exists b2. *)
    (*   simpl. rewrite Hb. assumption. *)
    (* + destruct IHhe3'' as [ b3 ]. *)
    (*   exists b3. *)
    (*   simpl. rewrite Hb. *)
    (*   assumption. *)
  - inversion H.
  - (* hle *) admit.
    (*  inversion H. *)
    (* subst. *)
    (* specialize (IHhe1 TNat H2). *)
    (* specialize (IHhe2 TNat H3). *)
    (* destruct IHhe1 as [ IHhe1' IHhe1'' ]. *)
    (* destruct IHhe2 as [ IHhe2' IHhe2'' ]. *)
    (* clear IHhe1''. *)
    (* clear IHhe2''. *)
    (* specialize (IHhe1' eq_refl). *)
    (* specialize (IHhe2' eq_refl). *)
    (* inversion IHhe1' as [ n1 Hn1 ]. *)
    (* inversion IHhe2' as [ n2 Hn2 ]. *)
    (* exists (Nat.leb n1 n2). *)
    (* simpl. rewrite Hn1. rewrite Hn2. *)
    (* reflexivity. *)
  - admit.
  - admit.
Admitted.
 
Lemma type_correct_nat :
  forall he : HExp,
    typing he TNat ->
    forall hl hr,
      hsem he (hl, hr) ->
      exists n, hr = HRNat n.
Proof.
  intros.
  assert (Hn : 
             hsem he (hl, hr) ->
             (TNat = TNat -> exists n, hr = HRNat n) /\
             (TNat = TBool -> exists b, hr = HRBool b)).
  apply type_correct; trivial.
  destruct Hn as [ H1 H2 ].
  assumption.
  apply H1.
  reflexivity.
Qed.

Lemma type_correct_bool :
  forall he : HExp,
    typing he TBool ->
    forall hl hr,
      hsem he (hl, hr) ->
    exists b, hr = HRBool b.
Proof.
  intros.
  assert (Hb :
            hsem he (hl, hr) ->
            (TBool = TNat -> exists n, hr = HRNat n) /\
            (TBool = TBool -> exists b, hr = HRBool b)).
  apply type_correct; trivial.
  destruct Hb as [ H1 H2 ].
  assumption.
  apply H2.
  reflexivity.
Qed.

(* Theorem tilde_app : *)
(*   tilde (hl1, hr1) (ll1, lr1) -> *)
(*   tilde (hl2, hr2) (ll2, lr2) -> *)

Definition translate (hr : HResult) : LResult :=
  match hr with
  | HRNat n => LRNat n
  | HRBool true => LRNat 1
  | HRBool false => LRNat 0
  | HRError => LRNat 0
  end.

Theorem tilde_translate :
  forall l x,
    not (x = HRError) ->
    tilde (l, x) (l, translate x).
Proof.
  unfold translate.
  destruct x.
  - destruct b.
    + constructor.
    + constructor.
  - simpl. split.
    + reflexivity.
    + reflexivity.
  - intros. apply H. reflexivity.
Qed.

Theorem type_soundness :
  forall he hl hr t,
    typing he t ->
    hsem he (hl, hr) ->
    hr <> HRError.
Proof.
  intros.
  destruct t.
  - assert (exists n : nat, hr = HRNat n).
    { eapply type_correct_nat.
      apply H.
      apply H0. }
    destruct H1.
    subst.
    intro Hcontra.
    inversion Hcontra.
  - assert (exists b : bool, hr = HRBool b).
    { eapply type_correct_bool.
      apply H.
      apply H0. }
    destruct H1.
    subst.
    intro Hcontra.
    inversion Hcontra.
Qed.

Theorem correct_compiler : forall he : HExp, forall t : type,
      typing he t ->
      forall l hr,
        hsem he (l, hr) ->
        exists lr,
          tilde (l, hr) (l, lr) /\ lsem (compile he) (l, lr).
Proof.
  induction he; intros t Ht l hr HS; exists (translate hr);     inversion Ht; subst; inversion HS; subst.
  - split.
    + split; reflexivity.
    + constructor.
  - destruct b.
    + split.
      * split; reflexivity.
      * constructor.
    + split.
      * split; reflexivity.
      * constructor.
  - (* HPlus *)
    specialize (IHhe1 TNat H1 hl1 (HRNat n1) H4).
    specialize (IHhe2 TNat H3 hl2 (HRNat n2) H6).
    inversion IHhe1 as [ lr1 ]. subst.
    inversion IHhe2 as [ lr2 ]. subst.
    destruct lr1 as [ x1 ].
    destruct lr2 as [ x2 ].
    inversion H.
    destruct H.
    destruct H.
    simpl in *.
    subst.
    destruct H0.
    destruct H0.
    simpl in *.
    subst.
    split.
    + split; reflexivity.
    + simpl. constructor.
      * assumption.
      * assumption.
  - (* HPlus error *)
    exfalso. 
    assert (Hcontra : exists n, HRError = HRNat n).
    { apply (type_correct_nat (HPlus he1 he2) (type_plus he1 he2 H1 H3) l).
      assumption. }
    inversion Hcontra. inversion H.
  - (* HPlus error left *)
    assert (Hcontra : exists n, HRError = HRNat n).
    { apply (type_correct_nat he1 H1 l).
      assumption. }
    inversion Hcontra. inversion H.
  - (* HPlus bool right *)
    assert (Hcontra : exists n, HRBool b2 = HRNat n).
    { apply (type_correct_nat he2 H3 hl2).
      assumption. }
    inversion Hcontra. inversion H.
  - (* HPlus error right *)
    assert (Hcontra : exists n, HRError = HRNat n).
    { apply (type_correct_nat he2 H3 hl2).
      assumption. }
    inversion Hcontra. inversion H.
  - (* HRTimes *)
    specialize (IHhe1 TNat H1 hl1 (HRNat n1) H4).
    specialize (IHhe2 TNat H3 hl2 (HRNat n2) H6).
    inversion IHhe1 as [ lr1 ]. subst.
    inversion IHhe2 as [ lr2 ]. subst.
    destruct lr1 as [ x1 ].
    destruct lr2 as [ x2 ].
    inversion H.
    destruct H.
    destruct H.
    simpl in *.
    subst.
    destruct H0.
    destruct H0.
    simpl in *.
    subst.
    split.
    + split; reflexivity.
    + simpl. constructor.
      * assumption.
      * assumption.
  - (* HTimes error *)
    exfalso. 
    assert (Hcontra : exists n, HRError = HRNat n).
    { apply (type_correct_nat (HTimes he1 he2) (type_times he1 he2 H1 H3) l).
      assumption. }
    inversion Hcontra. inversion H.
  - (* HTimes error left *)
    assert (Hcontra : exists n, HRError = HRNat n).
    { apply (type_correct_nat he1 H1 l).
      assumption. }
    inversion Hcontra. inversion H.
  - (* HTimes bool right *)
    assert (Hcontra : exists n, HRBool b2 = HRNat n).
    { apply (type_correct_nat he2 H3 hl2).
      assumption. }
    inversion Hcontra. inversion H.
  - (* HTimes error right *)
    assert (Hcontra : exists n, HRError = HRNat n).
    { apply (type_correct_nat he2 H3 hl2).
      assumption. }
    inversion Hcontra. inversion H.
  - (* HIte true *)
    specialize (IHhe1 TBool H2 hl1 (HRBool true) H1).
    specialize (IHhe2 t H4 hl2 hr H8).
    inversion IHhe1 as [ lr1 ]. subst.
    inversion IHhe2 as [ lr2 ]. subst.
    destruct lr1 as [ x1 ].
    destruct lr2 as [ x2 ].
    clear IHhe3.
    clear IHhe2.
    clear IHhe1.
    split.
    + apply tilde_translate.
      inversion H.
      destruct H.
      destruct H0.
      eapply type_soundness.
      apply H4.
      apply H8.
    + simpl.
      replace hl2 with (nil ++ hl2).
      remember (translate hr) as thr.
      destruct thr. 
      eapply LSIteRight.
      * apply H.
      * constructor.
      * destruct H.
        unfold tilde in H.
        destruct x1 as [ | x1' ]. 
        *** exfalso. apply H.
        *** intro Hcontra. inversion Hcontra.
      * destruct H0.
        assert (Hnoterr : hr <> HRError).
        { eapply type_soundness. apply H4. apply H8. }
        rewrite Heqthr.
        assert (tilde (hl2, hr) (hl2, translate hr)).
        { apply tilde_translate. assumption. }
        destruct hr.
        ** simpl in Heqthr.
           destruct b.
           *** destruct Heqthr.
               clear Hnoterr.
               unfold translate.
               unfold tilde in H0.
               destruct x2.
               exfalso. apply H0.
               destruct x2.
               assumption.
               exfalso. apply H0.
           *** destruct Heqthr.
               clear Hnoterr.
               unfold translate.
               unfold tilde in H0.
               destruct x2.
               assumption.
               exfalso. apply H0.
        ** unfold translate in *. inversion Heqthr.
           unfold tilde in H0. subst.
           inversion H0. subst.
           assumption.
        ** exfalso. apply Hnoterr. reflexivity.
      * reflexivity.
  - (* HIte false *)
    specialize (IHhe1 TBool H2 hl1 (HRBool false) H1).
    specialize (IHhe3 t H5 hl3 hr H8).
    inversion IHhe1 as [ lr1 ]. subst.
    inversion IHhe3 as [ lr3 ]. subst.
    destruct lr1 as [ x1 ].
    destruct lr3 as [ x3 ].
    clear IHhe3.
    clear IHhe2.
    clear IHhe1.
    split.
    + apply tilde_translate.
      inversion H.
      destruct H.
      destruct H0.
      eapply type_soundness.
      apply H5.
      apply H8.
    + simpl.
      replace hl3 with (nil ++ hl3).
      remember (translate hr) as thr.
      destruct thr. 
      eapply LSIteLeft.
      * apply H.
      * constructor.
      * destruct H.
        unfold tilde in H.
        destruct x1 as [ | x1' ]. 
        ** apply le_n.
        ** exfalso. apply H.
      * destruct H0.
        assert (Hnoterr : hr <> HRError).
        { eapply type_soundness. apply H5. apply H8. }
        rewrite Heqthr.
        assert (tilde (hl3, hr) (hl3, translate hr)).
        { apply tilde_translate. assumption. }
        destruct hr.
        ** simpl in Heqthr.
           destruct b.
           *** destruct Heqthr.
               clear Hnoterr.
               unfold translate.
               unfold tilde in H0.
               destruct x3.
               exfalso. apply H0.
               destruct x3.
               assumption.
               exfalso. apply H0.
           *** destruct Heqthr.
               clear Hnoterr.
               unfold translate.
               unfold tilde in H0.
               destruct x3.
               assumption.
               exfalso. apply H0.
        ** unfold translate in *. inversion Heqthr.
           unfold tilde in H0. subst.
           inversion H0. subst.
           assumption.
        ** exfalso. apply Hnoterr. reflexivity.
      * reflexivity.
  - (* HIte error *)
    assert (HRError <> HRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    contradiction H. reflexivity.
  - (* HIte error *)
    assert (HRError <> HRError).
    eapply type_soundness.
    apply H2.
    apply H0.
    contradiction H. reflexivity.
  - (* HLe *)
    specialize (IHhe1 TNat H1 hl1 (HRNat n1) H4).
    specialize (IHhe2 TNat H3 hl2 (HRNat n2) H6).
    inversion IHhe1 as [ lr1 ]. subst.
    inversion IHhe2 as [ lr2 ]. subst.
    destruct lr1 as [ x1 ].
    destruct lr2 as [ x2 ].
    inversion H.
    destruct H.
    destruct H.
    simpl in *.
    subst.
    destruct H0.
    destruct H0.
    simpl in *.
    subst.
    remember (Nat.leb x1 x2) as b.
    destruct b.
    + split.
      * reflexivity.
      * replace hl2 with (hl2 ++ []).
        eapply LSIteLeft.
        apply H7.
        apply H8.
        apply PeanoNat.Nat.leb_le.
        symmetry.
        apply Heqb.
        constructor.
        rewrite app_nil_end.
        reflexivity.
    + split.
      * reflexivity.
      * replace hl2 with (hl2 ++ []).
        eapply LSIteRight.
        apply H7.
        apply H8.
        rewrite <- PeanoNat.Nat.leb_le.
        rewrite <- Heqb.
        intro Hcontra.
        inversion Hcontra.
        constructor.
        rewrite app_nil_end.
        reflexivity.
  - (* HLe error *)
    assert (HRError <> HRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    contradiction H. reflexivity.
  - (* HLe error *)
    assert (HRError <> HRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    contradiction H. reflexivity.
  - (* HLe error *)
    assert (HRError <> HRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    contradiction H. reflexivity.
  - (* HLe error *)
    assert (HRError <> HRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    contradiction H. reflexivity.
  - split.
    + unfold tilde.
      unfold translate.
      split; reflexivity.
    + unfold translate.
      constructor.
Qed.

Require Import LanguageModel.
Require Import ChainModel.
Require Import NonRobustTraceCriterion.

Section Source.

  Definition sprg := {e : HExp | exists τ, typing e τ }.
  Definition spar := sprg.
  Definition sctx := unit.
  Definition splug (p : spar) (c : sctx) := p.

  Definition source := {| prg := sprg; par := spar; ctx := sctx; plug := splug |}.

  Definition traceS := HTrace.

  (* 
Lemma type_correct_nat :
  forall he : HExp,
    typing he TNat ->
    forall hl hr,
      hsem he (hl, hr) ->
      exists n, hr = HRNat n.
   *)
  
  Definition semS : sprg -> traceS -> Prop := fun p t => hsem (proj1_sig p) t.

(* this does not work yet 
  Definition semanticsS : Semantics source traceS.
  Proof.
    exists semS.
    destruct W as [e [[|] Hty]].
    - destruct (type_correct_nat e Hty) as [n Hn].
      now (exists (HTNat n)).
    - destruct (type_correct_bool _ Hty) as [b Hb].
      now (exists (HTBool b)).
  Defined.
*)

End Source.

(* Section Target. *)
(*   Definition tprg := LExp. *)
(*   Definition tpar := tprg. *)
(*   Definition tctx := unit. *)
(*   Definition tplug (p : tpar) (c : tctx) := p. *)

(*   Definition target := {| prg := tprg; par := tpar; ctx := tctx; plug := tplug |}. *)

(*   Definition traceT := LTrace. *)

(*   Definition semT : tprg -> traceT -> Prop := fun p t => lsem p = t. *)
(*   Definition semanticsT : Semantics target traceT. *)
(*   Proof. *)
(*     exists semT. *)
(*     destruct W; now eexists. *)
(*   Defined. *)

(* End Target. *)

(* Section CompilationChain. *)
(*   Definition compile_w : prg source -> prg target := *)
(*     fun (p : prg source) => compile (proj1_sig p). *)

(*   Definition compiler : CompilationChain source target := *)
(*     {| compile_whole := compile_w; compile_par := compile_w; compile_ctx := id |}. *)

(* End CompilationChain. *)

(* Definition rel_TC := rel_TC compiler semanticsS semanticsT tilde. *)

(* Lemma correctness : rel_TC. *)
(* Proof. *)
(*   unfold rel_TC. *)
(*   unfold NonRobustTraceCriterion.rel_TC. *)
(*   intros [es Hty] tt Hsem. *)
(*   inversion Hty as [τ Hty']. *)
(*   apply correct_compiler in Hty'. *)
(*   exists (hsem es). split; last now auto. *)
(*   simpl in Hsem. now rewrite Hsem in Hty'. *)
(* Qed. *)
