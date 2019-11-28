From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Require Import Setoid.
Require Export Classical.


Section labels.

Variable outputs : Type.
Variable inputs : Type.


Inductive label : Type :=
 | silent : label
 | inp : inputs -> label
 | out : outputs -> label
 | special : label.


End labels.

Arguments inp [_] [_] _.
Arguments out [_] [_] _.
Arguments silent [_] [_].
Arguments special [_] [_].


Structure LTS : Type := lts {
  carrier : Type;
  inputs : Type;
  outputs : Type;
  final : carrier -> Prop;
  trans : label outputs inputs -> relation carrier;
  final_stops : forall l P Q, final P -> (trans l P Q -> False) }.

Arguments trans [_] _ _ _.
Arguments final [_] _.

Coercion carrier : LTS >-> Sortclass.

Definition labels (T : LTS) := label (outputs T) (inputs T).

Definition is_input {outputs : Type} {inputs : Type} (l : label outputs inputs) := match l with
 | inp _ => True
 | _ => False
end.

Definition input_total (T : LTS) := forall P Q (i : inputs T), trans (inp i) P Q -> forall (j : inputs T), exists Q', trans (inp j) P Q' .

Definition determinate (T : LTS) := forall (P Q Q' : T) (l l' : labels T), trans l P Q -> trans l' P Q' -> ((l = l' /\ Q = Q') \/ (is_input l /\ is_input l')).
Definition determinate_inputs (T : LTS) := forall (P Q Q' : T) (i : inputs T), trans (inp i) P Q -> trans (inp i) P Q' -> Q = Q'.


Section Star.
Variable T : LTS.

Inductive Star_left : (labels T) -> relation T :=
 | star_inp : forall P Q i, trans (inp i) P Q -> Star_left (inp i) P Q
 | star_out : forall P Q o, trans (out o) P Q -> Star_left (out o) P Q
 | star_spec : forall P Q, trans special P Q -> Star_left special P Q
 | star_silent : forall P P' Q l, Star_left l P' Q -> trans silent P P' -> Star_left l P Q.


Definition stuck P := (~ final P) /\ forall Q (l : labels T), ~ (Star_left l P Q).


Lemma types_of_prgrs : forall (P : T), final P \/ stuck P \/ exists l Q, Star_left l P Q.
intro P.
destruct (classic (exists l Q, Star_left l P Q)).
+ right. right. assumption.
+ destruct (classic (final P)).
  - left. assumption.
  - right. left. unfold stuck. split. assumption.
    intros Q l F. apply H. exists l. exists Q. assumption.
Qed.


Lemma nonstuck : forall P, ~ stuck P -> (final P \/ exists l Q, Star_left l P Q).
intros P F.
destruct (classic (final P)).
left; assumption.
destruct (classic (exists l Q, Star_left l P Q)).
right; assumption.
destruct F.
split. apply H. intros Q l.
intro F. apply H0. exists l.
 exists Q. apply F.
Qed.


Lemma star_trans : forall (l : labels T) P Q, Star_left l P Q -> exists l' Q', trans l' P Q'.
intros l P Q H.
inversion H; subst. exists (inp i). exists Q. apply H0.
exists (out o). exists Q. apply H0.
exists special. exists Q. apply H0.
exists silent. exists P'. apply H1.
Qed.

Lemma starleft_silent: forall P Q, ~ Star_left silent P Q.
assert (forall P Q (l : labels T), Star_left l P Q -> silent = l -> False).
intros P Q l F eq.
induction F.
+ inversion eq.
+ inversion eq.
+ inversion eq.
+ apply IHF. assumption.
+ intros P Q F. eapply H. eassumption. trivial.
Qed.




End Star.

Arguments stuck [_] _.

Lemma det_starleft : forall T, determinate T -> forall (P Q Q' : T) (l l' : labels T), Star_left l P Q -> Star_left l' P Q' -> ((l = l' /\ Q = Q') \/ (is_input l /\ is_input l')).
intros T det P Q Q' l l' starl. revert Q' l'.
induction starl as [P Q i trans| P Q o trans| P Q trans | P P0 Q l starl IHstarl trans].
+ intros Q' l' starl'.
  induction starl' as [P Q' j trans'| P Q' p trans'| P Q' trans' | P P0' Q' l' starl' IHstarl' trans'].
  - destruct (det P Q Q' (inp i) (inp j)  trans trans') as [temp|temp].
    * left. assumption.
    * right. assumption.
  - destruct (det P Q Q' (inp i) (out p)  trans trans') as [temp|temp]; exfalso; destruct temp as [false1 false2]; inversion false1; inversion false2.
  - destruct (det P Q Q' (inp i) (special)  trans trans') as [temp|temp]; exfalso; destruct temp as [false1 false2]; inversion false1; inversion false2.
  - destruct (det P Q P0' (inp i) (silent)  trans trans') as [temp|temp]; exfalso; destruct temp as [false1 false2]; inversion false1; inversion false2.
+ intros Q' l' starl'.
  induction starl' as [P Q' j trans'| P Q' p trans'| P Q' trans' | P P0' Q' l' starl' IHstarl' trans'].
  - destruct (det P Q Q' (out o) (inp j)  trans trans') as [temp|temp]; exfalso; destruct temp as [false1 false2]; inversion false1; inversion false2.
  - destruct (det P Q Q' (out o) (out p)  trans trans') as [temp|temp].
    * left. assumption.
    * right. assumption.
  - destruct (det P Q Q' (out o) (special)  trans trans') as [temp|temp]; exfalso; destruct temp as [false1 false2]; inversion false1; inversion false2.
  - destruct (det P Q P0' (out o) (silent)  trans trans') as [temp|temp]; exfalso; destruct temp as [false1 false2]; inversion false1; inversion false2.
+ intros Q' l' starl'.
  induction starl' as [P Q' j trans'| P Q' p trans'| P Q' trans' | P P0' Q' l' starl' IHstarl' trans'].
  - destruct (det P Q Q' (special) (inp j)  trans trans') as [temp|temp]; exfalso; destruct temp as [false1 false2]; inversion false1; inversion false2.
  - destruct (det P Q Q' (special) (out p)  trans trans') as [temp|temp]; exfalso; destruct temp as [false1 false2]; inversion false1; inversion false2.
  - destruct (det P Q Q' (special) (special)  trans trans') as [temp|temp].
    * left. assumption.
    * right. assumption.
  - destruct (det P Q P0' (special) (silent)  trans trans') as [temp|temp]; exfalso; destruct temp as [false1 false2]; inversion false1; inversion false2.
+  intros Q' l' starl'.
   induction starl' as [P Q' j trans'| P Q' p trans'| P Q' trans' | P P0' Q' l' starl' IHstarl' trans'].
  - destruct (det P P0 Q' (silent) (inp j)  trans trans') as [temp|temp]; exfalso; destruct temp as [false1 false2]; inversion false1; inversion false2.
  - destruct (det P P0 Q' (silent) (out p)  trans trans') as [temp|temp]; exfalso; destruct temp as [false1 false2]; inversion false1; inversion false2.
  - destruct (det P P0 Q' (silent) (special)  trans trans') as [temp|temp]; exfalso; destruct temp as [false1 false2]; inversion false1; inversion false2.
  - destruct (det P P0 P0' (silent) (silent)  trans trans') as [temp|temp]. destruct temp as [_ eq]. subst.
    apply IHstarl. assumption.
  - destruct temp as [false1 false2]; inversion false1.
Qed.


Lemma det_starleft_inputs : forall (T : LTS), determinate T -> determinate_inputs T -> forall (P Q Q' : T) (i : inputs T), Star_left (inp i) P Q -> Star_left (inp i) P Q' -> Q = Q'.
intros T det deti P Q Q' i starl starl'.
remember (inp i) as l.
induction starl.
+ remember (inp i0) as l'.
  induction starl' as [P Q' j trans'| P Q' p trans'| P Q' trans' | P P0' Q' l' starl' IHstarl' trans']; try inversion Heql.
  - unfold determinate_inputs in deti. eapply deti; eassumption.
  - subst. exfalso. edestruct det. apply H. apply trans'. destruct H1. inversion H1.
  - destruct H1. inversion H2.
+ inversion Heql.
+ inversion Heql.
+ induction starl'.
  - subst. exfalso. edestruct det. apply H. apply H0. destruct H1. inversion H1.
  - destruct H1. inversion H1.
  - inversion Heql.
  - inversion Heql.
  - subst. apply IHstarl. trivial.
    edestruct det.
    * apply H. apply H0. destruct H1. subst. assumption.
    * destruct H1. inversion H1.
Qed.



Lemma inputotal_starleft : forall T, input_total T -> forall P Q (i : inputs T), Star_left (inp i) P Q -> forall (j : inputs T), exists Q', Star_left (inp j) P Q' .
intros T IT P Q.
assert (forall (l : labels T), Star_left l P Q -> forall (i : inputs T), l = inp i -> forall (j : inputs T), exists Q', Star_left (inp j) P Q').
intros l starl.
induction starl; intros i' eq j.
+ inversion eq. subst. unfold input_total in IT. destruct (IT P Q i' H j) as [Q' trans']. exists Q'. constructor. assumption.
+ inversion eq.
+ inversion eq.
+ destruct (IHstarl i' eq j) as [Q' starl']. exists Q'. eapply star_silent. eassumption. assumption.
intros i starl j.
edestruct (H (inp i) starl) as [Q' starl'].
reflexivity.
exists Q'.
eassumption.
Qed.



Section Forward_backward.

Variable source : LTS.
Variable target : LTS.
Hypothesis source_det : determinate source.
Hypothesis target_det : determinate target.
Hypothesis source_total: input_total source.
Variable rel_inp : inputs source -> inputs target -> Prop.
Variable rel_out : outputs source -> outputs target -> Prop.
Hypothesis rel_total_inp : forall (j : inputs target), exists (i : inputs source), rel_inp i j.

Definition forward_props (R : source -> target -> Prop) (P : source) (P' : target) := 
 (final P /\ final P') \/ (~ final P /\ ~ final P' /\ 
  ( (exists Q, Star_left special P Q)
 \/ (exists Q', Star_left special P' Q')
 \/ ((stuck P <-> stuck P')
     /\ (forall i Q, Star_left (inp i) P Q -> exists Q' j, rel_inp i j /\ Star_left (inp j) P' Q' /\ R Q Q')
     /\ (forall o Q, Star_left (out o) P Q -> exists Q' p, rel_out o p /\ Star_left (out p) P' Q' /\ R Q Q')))).

Definition backward_props (R : source -> target -> Prop) (P : source) (P' : target) := 
 (final P /\ final P') \/ (~ final P /\ ~ final P' /\ 
  ( (exists Q, Star_left special P Q)
 \/ (exists Q', Star_left special P' Q')
 \/ ((stuck P' <-> stuck P)
     /\ (forall j Q', Star_left (inp j) P' Q' -> exists Q i, rel_inp i j /\ Star_left (inp i) P Q /\ R Q Q')
     /\ (forall p Q', Star_left (out p) P' Q' -> exists Q o, rel_out o p /\ Star_left (out o) P Q /\ R Q Q')))).



Definition forward_sim (R : source -> target -> Prop) := forall P Q, R P Q -> forward_props R P Q.
Definition backward_sim (R : source -> target -> Prop) := forall P Q, R P Q -> backward_props R P Q.



Definition locally_flippable (R : source -> target -> Prop) (P : source) (P' : target) : Prop := forall Q Q' i j, 
 Star_left (inp i) P Q 
 -> Star_left (inp j) P' Q' 
 -> rel_inp i j 
 -> exists i0 Q0, rel_inp i0 j /\ Star_left (inp i0) P Q0 /\ R Q0 Q'.

Definition flippable (R : source -> target -> Prop) := forall P P', R P P' -> locally_flippable R P P'.



Section Flip.
Variable R : source -> target -> Prop.
Variable P : source.
Variable P' : target.
Hypothesis fwd : forward_props R P P'.
Hypothesis flippable : locally_flippable R P P'.

Lemma flipping_lemma : backward_props R P P'.
destruct fwd as [fin | fwd'].
+ left. assumption.
+ destruct fwd' as [notfin1 fwd']; destruct fwd' as [notfin2 fwd'].
  destruct (types_of_prgrs source P) as [fin | other].
  - exfalso. apply notfin1. assumption.
  - destruct fwd' as [spec | fwd'']; [| destruct fwd'' as [spec'|step]].
    * right. split. assumption. split. assumption. left. assumption.
    * right. split. assumption. split. assumption. right. left. assumption.
    * destruct step as [stk step']. destruct step' as [stepinp stepout]. destruct stk as [stk1 stk2].
      destruct other as [stk0|prod].
      + right. split; [assumption|]. split; [assumption|]. right. right. split. split; assumption.
        split.
        - intros j Q' sleft. exfalso. destruct (stk1 stk0) as [notfin notstarleft]. apply (notstarleft Q' (inp j) sleft).
        - intros p Q' sleft. exfalso. destruct (stk1 stk0) as [notfin notstarleft]. apply (notstarleft Q' (out p) sleft).
      + destruct prod as [l prod']. destruct prod' as [Q sleft]. induction l.
        * exfalso. apply (starleft_silent sleft).
        * right. split ; [assumption|split;[assumption|]]. right. right. split. split; assumption.
          destruct (stepinp i Q sleft) as [Q' temp].
          destruct temp as [j temp]. destruct temp as [relop temp]. destruct temp as [sleft' RQQ'].
          split.
          - intros j' Q'' sleft''.
            * destruct (rel_total_inp j') as [i' relop'].
              destruct (inputotal_starleft source_total sleft i') as [Q0 sleft0].
              destruct (stepinp i' Q0 sleft0) as [Q0' sleft0']. destruct sleft0' as [j0 sleft0'].
              destruct sleft0' as [relop0 sleft0']. destruct sleft0' as [sleft0' RQQ0].
              destruct flippable with Q0 Q'' i' j' as [iF HF]. assumption. assumption. assumption.
              destruct HF as [QF HF]. destruct HF as [relinpF HF]. destruct HF as [StarlF RQ0Q'].
              exists QF. exists iF. split; [|split].
              - assumption.
              - assumption.
              - assumption.
          - intros p Q'' sleft''. exfalso. destruct (det_starleft target_det sleft' sleft'') as [false1|false2].
            * destruct false1 as [eqfalse eq]. inversion eqfalse.
            * destruct false2 as [isinp false]. inversion false.
        * right. split ; [assumption|split;[assumption|]]. right. right. split. split; assumption.
          destruct (stepout o Q sleft) as [ Q' temp]. 
          destruct temp as [p temp]. destruct temp as [relop temp]. destruct temp as [sleft' RQQ'].
          split.
          - intros j Q'' sleft''. exfalso. destruct (det_starleft target_det sleft' sleft'') as [false1|false2]. 
            + destruct false1 as [eq1 eq2]. inversion eq1.
            + destruct false2 as [isinp1 isinp2]. inversion isinp1.
          - intros p' Q'' sleft''. destruct (det_starleft target_det sleft' sleft'') as [eq|isinp].
            + destruct eq as [eq eq']. inversion eq. subst. exists Q. exists o.
              split. assumption. split; assumption.
            + exfalso. destruct isinp as [false1 false2]. inversion false1. 
        * right. split ; [assumption|split;[assumption|]]. left. exists Q. apply sleft.
Qed.


End Flip.



Theorem flip : forall R, forward_sim R -> flippable R -> backward_sim R.
intros R fwd flb P Q RPQ.
apply flipping_lemma.
+ apply fwd.
  assumption.
+ apply flb.
  assumption.
Qed.



Section Bijection_flip.
Hypothesis bij : forall i j j', rel_inp i j -> rel_inp i j' -> j = j'.
Hypothesis inpdet : determinate_inputs target.

Lemma sim_inp_case : forall (R : source -> target -> Prop) P P' Q i, 
 R P P' -> Star_left (inp i) P Q -> forward_sim R 
 -> (exists Q', Star_left special P' Q') \/ (exists Q' j, rel_inp i j /\ Star_left (inp j) P' Q' /\ R Q Q').
intros R P P' Q i RPP' starl fwd.
destruct (star_trans starl) as [l tr]. destruct tr as [Q'' tr].
destruct fwd with P P'. assumption.
+ destruct H as [F F']. exfalso. eapply final_stops. eapply F. eassumption.
+ destruct H as [_ H]. destruct H as [_ H]. destruct H.
  - exfalso. destruct H as [Qs trs]. edestruct det_starleft; [|eapply starl| | |]. eapply source_det.  eapply trs.
    destruct H. inversion H.
  - destruct H. inversion H0.
+ destruct H.
  - left. apply H.
  - destruct H as [_ H]. destruct H as [H _].
    right.
    apply H. assumption.
Qed.



Lemma bij_flippable : forall R, forward_sim R -> flippable R.
intros R fwd P P' RPP' Q Q' i j starl starl' relinp.
edestruct sim_inp_case; try eassumption.
+ exfalso. destruct H as [Qs trs].
  edestruct det_starleft. apply target_det. 
  apply starl'.
  apply trs.
  destruct H. inversion H.
  destruct H. inversion H0.
+ destruct H as [Q'' H]. destruct H as [j' H]. destruct H as [relinp' H].
  destruct H as [starl'' RQQ''].
  assert (j = j').
  apply bij with i. apply relinp. apply relinp'.
  subst.
  exists i. exists Q. split; [|split]; try assumption.
  assert (Q' = Q''). eapply det_starleft_inputs. assumption. assumption.
  eapply starl'. eassumption.
  subst. assumption. 
Qed.

Theorem bij_flip : forall R, forward_sim R -> backward_sim R.
intros R fwd.
apply flip.
+ apply fwd.
+ apply bij_flippable. apply fwd.
Qed.




End Bijection_flip.

End Forward_backward.