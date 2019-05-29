Require Import LanguageModel.
Require Import ChainModel.
Require Import NonRobustTraceCriterion.


Inductive HExp :=
  HNat : nat -> HExp
| HBool : bool -> HExp
| HPlus : HExp -> HExp -> HExp
| HTimes : HExp -> HExp -> HExp
| HIte : HExp -> HExp -> HExp -> HExp
| HLe : HExp -> HExp -> HExp.

Inductive LExp :=
  LNat : nat -> LExp
| LPlus : LExp -> LExp -> LExp
| LTimes : LExp -> LExp -> LExp
| LIte : LExp -> LExp -> LExp -> LExp -> LExp.

Fixpoint compile (he : HExp) : LExp :=
  match he with
    HNat n => LNat n
  | HBool true => LNat 1
  | HBool false => LNat 0
  | HPlus he1 he2 => LPlus (compile he1) (compile he2)
  | HTimes he1 he2 => LTimes (compile he1) (compile he2)
  | HLe he1 he2 => LIte (compile he1) (compile he2) (LNat 1) (LNat 0)
  | HIte he1 he2 he3 => LIte (compile he1) (LNat 0) (compile he3) (compile he2)
  end.

Inductive HTrace :=
| HTBool : bool -> HTrace
| HTNat : nat -> HTrace
| HTError : HTrace.

Inductive LTrace :=
| LTNat : nat -> LTrace.

Fixpoint hsem (he : HExp) : HTrace :=
  match he with
  | HNat nat => HTNat nat
  | HBool bool => HTBool bool
  | HPlus he1 he2 => match (hsem he1, hsem he2) with
                       (HTNat n1, HTNat n2) => HTNat (plus n1 n2)
                     | (HTNat _, HTBool _) => HTError
                     | (HTNat _, HTError) => HTError
                     | (HTBool b1, _) => HTError
                     | (HTError, _) => HTError
                     end
  | HTimes he1 he2 => match (hsem he1, hsem he2) with
                       (HTNat n1, HTNat n2) => HTNat (mult n1 n2)
                     | (HTNat _, HTBool _) => HTError
                     | (HTNat _, HTError) => HTError
                     | (HTBool b1, _) => HTError
                     | (HTError, _) => HTError
                     end
  | HIte he1 he2 he3 => match hsem he1 with
                          (HTNat _) => HTError
                        | (HTBool true) => hsem he2
                        | (HTBool false) => hsem he3
                        | HTError => HTError
                        end
  | HLe he1 he2 => match (hsem he1, hsem he2) with
                     (HTNat n1, HTNat n2) => (HTBool (Nat.leb n1 n2))
                   | (_, _) => HTError
                   end
  end.

Fixpoint lsem (le : LExp) : LTrace :=
  match le with
  | LNat n => LTNat n
  | LPlus le1 le2 => match (lsem le1, lsem le2) with
                     | (LTNat n1, LTNat n2) => (LTNat (plus n1 n2))
                     end
  | LTimes le1 le2 => match (lsem le1, lsem le2) with
                      | (LTNat n1, LTNat n2) => (LTNat (mult n1 n2))
                      end
  | LIte le1 le2 le3 le4 => match (lsem le1, lsem le2) with
                            | (LTNat n1, LTNat n2) => match Nat.leb n1 n2 with
                                                        false => (lsem le4)
                                                      | true => (lsem le3)
                                                      end
                            end
  end.

Inductive tilde : HTrace -> LTrace -> Prop :=
| same_nat : forall n, tilde (HTNat n) (LTNat n)
| true_1 : tilde (HTBool true) (LTNat 1)
| false_0 : tilde (HTBool false) (LTNat 0).

(* another way this could be defined *)
Definition tilde' (ht:HTrace) (lt:LTrace) : Prop :=
  match ht, lt with
  | HTNat n1, LTNat n2 => n1 = n2
  | HTBool true, LTNat 1
  | HTBool false, LTNat 0 => True
  | _, _ => False
  end.

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
    typing (HLe he1 he2) TBool.

Theorem type_correct :
  forall he : HExp,
  forall t : type,
    typing he t ->
    (t = TNat -> exists n, hsem he = HTNat n) /\
    (t = TBool -> exists b, hsem he = HTBool b).
Proof.
  induction he; intros; split; intros; subst.
  - exists n. reflexivity.
  - inversion H.
  - inversion H.
  - exists b. reflexivity.
  - (* HPlus *) inversion H. subst.
    specialize (IHhe1 TNat H2).
    specialize (IHhe2 _ H3).
    destruct IHhe1 as [ IHhe1' IHhe1'' ].
    destruct IHhe2 as [ IHhe2' IHhe2'' ].
    clear IHhe1''.
    clear IHhe2''.
    specialize (IHhe1' eq_refl).
    specialize (IHhe2' eq_refl).
    inversion IHhe1' as [ n1 Hn1 ].
    inversion IHhe2' as [ n2 Hn2 ].
    exists (plus n1 n2).
    simpl. rewrite Hn1. rewrite Hn2. reflexivity.
  - inversion H.
  - (* HTimes *) inversion H. subst.
    specialize (IHhe1 TNat H2).
    specialize (IHhe2 _ H3).
    destruct IHhe1 as [ IHhe1' IHhe1'' ].
    destruct IHhe2 as [ IHhe2' IHhe2'' ].
    clear IHhe1''.
    clear IHhe2''.
    specialize (IHhe1' eq_refl).
    specialize (IHhe2' eq_refl).
    inversion IHhe1' as [ n1 Hn1 ].
    inversion IHhe2' as [ n2 Hn2 ].
    exists (mult n1 n2).
    simpl. rewrite Hn1. rewrite Hn2. reflexivity.
  - inversion H.
  - (* ite return TNat *) inversion H. subst.
    specialize (IHhe1 TBool H3).
    specialize (IHhe2 TNat H5).
    specialize (IHhe3 TNat H6).
    destruct IHhe1 as [ IHhe1' IHhe1'' ].
    destruct IHhe2 as [ IHhe2' IHhe2'' ].
    destruct IHhe3 as [ IHhe3' IHhe3'' ].
    clear IHhe1'.
    clear IHhe2''.
    clear IHhe3''.
    specialize (IHhe1'' eq_refl).
    specialize (IHhe2' eq_refl).
    specialize (IHhe3' eq_refl).
    inversion IHhe1'' as [ b Hb ].
    destruct b.
    + destruct IHhe2' as [ n2 ].
      exists n2.
      simpl. rewrite Hb. assumption.
    + destruct IHhe3' as [ n3 ].
      exists n3.
      simpl. rewrite Hb.
      assumption.
  - (* ite returning TBool *)
    inversion H. subst.
    specialize (IHhe1 TBool H3).
    specialize (IHhe2 TBool H5).
    specialize (IHhe3 TBool H6).
    destruct IHhe1 as [ IHhe1' IHhe1'' ].
    destruct IHhe2 as [ IHhe2' IHhe2'' ].
    destruct IHhe3 as [ IHhe3' IHhe3'' ].
    clear IHhe1'.
    clear IHhe2'.
    clear IHhe3'.
    specialize (IHhe1'' eq_refl).
    specialize (IHhe2'' eq_refl).
    specialize (IHhe3'' eq_refl).
    inversion IHhe1'' as [ b Hb ].
    destruct b.
    + destruct IHhe2'' as [ b2 ].
      exists b2.
      simpl. rewrite Hb. assumption.
    + destruct IHhe3'' as [ b3 ].
      exists b3.
      simpl. rewrite Hb.
      assumption.
  - inversion H.
  - (* hle *) inversion H.
    subst.
    specialize (IHhe1 TNat H2).
    specialize (IHhe2 TNat H3).
    destruct IHhe1 as [ IHhe1' IHhe1'' ].
    destruct IHhe2 as [ IHhe2' IHhe2'' ].
    clear IHhe1''.
    clear IHhe2''.
    specialize (IHhe1' eq_refl).
    specialize (IHhe2' eq_refl).
    inversion IHhe1' as [ n1 Hn1 ].
    inversion IHhe2' as [ n2 Hn2 ].
    exists (Nat.leb n1 n2).
    simpl. rewrite Hn1. rewrite Hn2.
    reflexivity.
Qed.

Lemma type_correct_nat : 
  forall he : HExp,
    typing he TNat ->
    exists n, hsem he = HTNat n.
Proof.
  intros.
  assert (Hn : (TNat = TNat -> exists n : nat, hsem he = HTNat n) /\
               (TNat = TBool -> exists b : bool, hsem he = HTBool b)).
  apply type_correct; trivial.
  destruct Hn as [ H1 H2 ].
  apply H1.
  reflexivity.
Qed.
    
Lemma type_correct_bool : 
  forall he : HExp,
    typing he TBool ->
    exists b, hsem he = HTBool b.
Proof.
  intros.
  assert (Hb : (TBool = TNat -> exists n : nat, hsem he = HTNat n) /\
               (TBool = TBool -> exists b : bool, hsem he = HTBool b)).
  apply type_correct; trivial.
  destruct Hb as [ H1 H2 ].
  apply H2.
  reflexivity.
Qed.
    
Theorem correct_compiler : forall he : HExp, forall t : type,
      typing he t ->
      tilde (hsem he) (lsem (compile he)).
Proof.
  induction he.
  - simpl. constructor.
  - simpl. destruct b.
    + simpl. constructor.
    + simpl. constructor.
  - (* HPlus *) intros.
    inversion H. subst.
    specialize (IHhe1 TNat H2).
    specialize (IHhe2 TNat H4).
    simpl.
    assert (Hn1 : exists n1, hsem he1 = HTNat n1).
    { apply type_correct_nat. assumption. }
    assert (Hn2 : exists n2, hsem he2 = HTNat n2).
    { apply type_correct_nat. assumption. }
    destruct Hn1 as [ n1 Hn1 ].
    destruct Hn2 as [ n2 Hn2 ].
    rewrite Hn1 in *.
    rewrite Hn2 in *.
    inversion IHhe1; subst.
    inversion IHhe2; subst.
    constructor.
  - (* HTimes *) intros.
    inversion H. subst.
    specialize (IHhe1 TNat H2).
    specialize (IHhe2 TNat H4).
    simpl.
    assert (Hn1 : exists n1, hsem he1 = HTNat n1).
    { apply type_correct_nat. assumption. }
    assert (Hn2 : exists n2, hsem he2 = HTNat n2).
    { apply type_correct_nat. assumption. }
    destruct Hn1 as [ n1 Hn1 ].
    destruct Hn2 as [ n2 Hn2 ].
    rewrite Hn1 in *.
    rewrite Hn2 in *.
    inversion IHhe1; subst.
    inversion IHhe2; subst.
    constructor.
  - (* HIte *) intros.
    inversion H. subst.
    specialize (IHhe1 TBool H3).
    specialize (IHhe2 t H5).
    specialize (IHhe3 t H6).
    simpl.
    remember (hsem he1) as semhe1.
    assert (Hb : exists b, hsem he1 = HTBool b).
    { apply type_correct_bool. assumption. }
    destruct semhe1.
    + destruct b.
      * inversion IHhe1. simpl. assumption.
      * inversion IHhe1. simpl. assumption.
    + rewrite <- Heqsemhe1 in *. inversion Hb. inversion H0.
    + rewrite <- Heqsemhe1 in *. inversion Hb. inversion H0.
  - (* HLe *) intros.
    inversion H. subst.
    specialize (IHhe1 TNat H2).
    specialize (IHhe2 TNat H4).
    simpl.
    assert (Hn1 : exists n1, hsem he1 = HTNat n1).
    { apply type_correct_nat. assumption. }
    assert (Hn2 : exists n2, hsem he2 = HTNat n2).
    { apply type_correct_nat. assumption. }
    destruct Hn1 as [ n1 Hn1 ].
    destruct Hn2 as [ n2 Hn2 ].
    rewrite Hn1 in *.
    rewrite Hn2 in *.
    inversion IHhe1; subst.
    inversion IHhe2; subst.
    remember (Nat.leb n1 n2) as b.
    destruct b; constructor.
Qed.



Section Source.

  Definition sprg := {e : HExp | exists τ, typing e τ }.
  Definition spar := sprg.
  Definition sctx := unit.
  Definition splug (p : spar) (c : sctx) := p.

  Definition source := {| prg := sprg; par := spar; ctx := sctx; plug := splug |}.

  Definition traceS := HTrace.

  Definition semS : sprg -> traceS -> Prop := fun p t => hsem (proj1_sig p) = t.
  Definition semanticsS : Semantics source traceS.
  Proof.
    exists semS.
    destruct W as [e [[|] Hty]].
    - destruct (type_correct_nat _ Hty) as [n Hn].
      now (exists (HTNat n)).
    - destruct (type_correct_bool _ Hty) as [b Hb].
      now (exists (HTBool b)).
  Defined.

End Source.

Section Target.
  Definition tprg := LExp.
  Definition tpar := tprg.
  Definition tctx := unit.
  Definition tplug (p : tpar) (c : tctx) := p.

  Definition target := {| prg := tprg; par := tpar; ctx := tctx; plug := tplug |}.

  Definition traceT := LTrace.

  Definition semT : tprg -> traceT -> Prop := fun p t => lsem p = t.
  Definition semanticsT : Semantics target traceT.
  Proof.
    exists semT.
    destruct W; now eexists.
  Defined.

End Target.

Section CompilationChain.
  Definition compile_w : prg source -> prg target :=
    fun (p : prg source) => compile (proj1_sig p).

  Definition compiler : CompilationChain source target :=
    {| compile_whole := compile_w; compile_par := compile_w; compile_ctx := id |}.

End CompilationChain.

Definition rel_TC := rel_TC compiler semanticsS semanticsT tilde.

Lemma correctness : rel_TC.
Proof.
  unfold rel_TC.
  unfold NonRobustTraceCriterion.rel_TC.
  intros [es Hty] tt Hsem.
  inversion Hty as [τ Hty'].
  apply correct_compiler in Hty'.
  exists (hsem es). split; last now auto.
  simpl in Hsem. now rewrite Hsem in Hty'.
Qed.



