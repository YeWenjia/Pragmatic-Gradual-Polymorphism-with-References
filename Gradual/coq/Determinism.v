Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Logic. Import Decidable.
Require Import
        Definitions
        Lemmas
        Infrastructure
        Soundness.



Lemma ptype_uniq: forall mu u A B,
 sto_ok mu ->
 pvalue u -> ptype mu u A -> ptype mu u B -> A = B.
Proof.
  introv ok pval ptyp1 ptyp2.
  inductions pval; try solve[inverts* ptyp1; inverts* ptyp2].
Qed.


Lemma TypedReduce_unique: forall P v mu r1 r2 (A: typ),
    sto_ok mu -> value v -> (exists B, typing nil P v Inf B) -> TypedReduce (v, mu) A r1 -> TypedReduce (v, mu) A r2 -> r1 = r2.
Proof.
  introv ok Val H R1 R2.
  gen r2.
  lets R1': R1.
  inductions R1; introv R2;
    try solve [inverts~ R2].
  -
  inverts~ R2.
  forwards*: ptype_uniq H0 H9. subst*.
  -
  inverts~ R2.
  forwards*: ptype_uniq H0 H9. subst*.
Qed.


Lemma  TypeLists_unique: forall v r1 r2 A P mu ,
    P |== mu -> value v -> (exists B, typing nil P v Inf B) ->  TypeLists (v,mu) A r1 ->  TypeLists (v,mu) A r2 -> r1 = r2.
Proof.
  introv ok Val H R1 R2.
  gen r2.
  lets R1': R1.
  inductions R1; introv R2;
    try solve [inverts* R2].
  - inverts* R2.
    inverts ok.
    forwards*: TypedReduce_unique H0 H6.
    congruence. 
  - inverts* R2.
    inverts ok.
    forwards*: TypedReduce_unique H0 H6.
    congruence.
    lets ok': ok.
    inverts ok.
    inverts H. 
    forwards*: TypedReduce_preservation H0.
    forwards*: TypedReduce_prv_value H0.
    forwards*: TypedReduce_unique H0 H6.
    inverts* H5.
Qed.


Lemma fill_eq: forall mu E0 e0 E e1 r1 r2 mu1 mu2,
  fill E0 e0 = fill E e1 ->
  step (e0, mu) (r1,mu1) ->
  step (e1, mu) (r2,mu2) ->
  wellformed E ->
  wellformed E0 ->
  E = E0 /\ e0 = e1.
Proof.
  introv eq red1 red2 wf1 wf2. gen mu mu1 mu2 E e0 e1 r1 r2.
  inductions E0; unfold fill in *;  intros;
  try solve[inductions E; unfold fill in *; inverts* eq;
  inverts wf1;
  forwards*: step_not_value red1];
  try solve[inductions E; unfold fill in *; inverts* eq];
  try solve[inductions E; unfold fill in *; inverts* eq;
  inverts wf2;
  forwards*: step_not_value red2].
Qed.


Lemma typing_chk: forall E e P A,
 typing E P e Inf A ->
 typing E P e Chk A.
Proof.
  introv typ.
  eapply typ_consist; eauto.
Qed.


Lemma typing_chk2: forall E e P A,
 typing E P e Inf A ->
 exists B, typing E P e Chk B /\ consist E A B.
Proof.
  introv typ.
  exists A. splits.
  eapply typ_consist; auto.
  eapply consist_refl;eauto.
Qed.


Lemma fill_chk: forall F e dir P A,
 typing empty P (fill F e) dir A ->
 exists B, typing empty P e Chk B.
Proof.
  introv typ.
  destruct F; unfold fill in *;inverts* typ.
  -
  forwards*: typing_chk H4.
  -
  inverts H0.
  forwards*: typing_chk H6.
  -
  inverts H0.
  forwards*: typing_chk H6.
  -
  inverts H0.
  forwards*: typing_chk H7.
  -
  inverts H0.
  forwards*: typing_chk H4.
  -
  inverts H0.
  forwards*: typing_chk H5.
  -
  inverts H0.
  forwards*: typing_chk H6.
  -
  forwards*: typing_chk H4.
  -
  inverts H0.
  exists*.
Qed.



Lemma pattern_abs_uniq: forall A B1 B2,
 pattern_abs A B1 ->
 pattern_abs A B2 ->
 B1 = B2.
Proof.
  introv pa1 pa2.
  inverts pa1; inverts* pa2.
Qed.


Lemma pattern_all_uniq: forall A B1 B2,
 pattern_all A B1 ->
 pattern_all A B2 ->
 B1 = B2.
Proof.
  introv pa1 pa2.
  inverts pa1; inverts* pa2.
Qed.


Lemma pattern_ref_uniq: forall A B1 B2,
 pattern_ref A B1 ->
 pattern_ref A B2 ->
 B1 = B2.
Proof.
  introv pa1 pa2.
  inverts pa1; inverts* pa2.
Qed.


Theorem step_unique: forall P mu A e r1 r2,
   P |== mu -> typing nil P e Chk A -> step (e, mu) r1 -> step (e, mu) r2 -> r1 = r2.
Proof.
  introv well Typ Red1.
  gen P A r2.
  lets Red1' : Red1.
  inductions Red1; 
    introv well Typ Red2.
  -
    inverts* Red2; 
    try solve[destruct F; unfold fill in H0; inverts* H0];
    try solve[
    forwards*: typing_regular Typ;destructs~ H1;destruct F; unfold fill in H0; inverts* H0;
    inverts* H5;
    inverts* H9;
    forwards: step_not_value Red1; auto; inverts H0];
    try solve[
    forwards*: typing_regular Typ;destructs~ H1;destruct F; unfold fill in H0; inverts* H0;
    inverts* H3;
    inverts* H7;
    forwards: step_not_value Red1; auto; inverts H0];
    try solve[ destruct F; unfold fill in *; inverts* H0;
    forwards: step_not_value Red1; auto; inverts* H0];
    try solve[destruct F; unfold fill in H5; inverts* H5].
    + forwards*: fill_eq H0.
      destruct H1. subst. inverts Typ.
      forwards*: fill_chk H3. inverts* H5.
      forwards*: IHRed1 Red1 H4. congruence.
    +  forwards*: fill_eq H0.
      destruct H1. subst. inverts Typ.
      forwards*: fill_chk H3. inverts* H5.
      forwards*: IHRed1 Red1 H4. congruence.
    +
     forwards*: typing_regular Typ.
     destructs~ H1. 
     destruct F; unfold fill in *; inverts* H0;
     try solve[inverts H6; inverts H10;forwards: step_not_value Red1; auto;inverts* H0].
    + forwards*: typing_regular Typ.
     destructs~ H1. 
     destruct F; unfold fill in *; inverts* H0;
     try solve[     inverts* H6;
     inverts* H10;
     forwards: step_not_value Red1; auto; inverts* H0].
    +
     forwards*: typing_regular Typ.
     destructs~ H1. 
     destruct F; unfold fill in *; inverts* H0;
     try solve[
     inverts* H4;
     inverts* H9;
     forwards: step_not_value Red1; auto; inverts* H0].
    +
      forwards*: typing_regular Typ.
     destructs~ H1. 
     destruct F; unfold fill in *; inverts* H0;
     try solve[
     inverts* H4;
     inverts* H9;
     forwards: step_not_value Red1; auto; inverts* H0].
    +
    forwards*: typing_regular Typ.
     destructs~ H1. 
     destruct F; unfold fill in *; inverts* H0;
     try solve[
     inverts* H3;
     inverts* H6;
     forwards: step_not_value Red1; auto; inverts* H0].
  -
    inverts Red2; 
    try solve[destruct F; unfold fill in H0; inverts H0];
    try solve[forwards: typing_regular Typ;
    destructs~ H1;
    destruct F; unfold fill in *; inverts H0;
    inverts H5;
    inverts H9;
    forwards: step_not_value Red1; auto; inverts H0];
    try solve[
      forwards: typing_regular Typ;
     destructs~ H1;
     destruct F; unfold fill in *; inverts H0;
     inverts H4;
     inverts H8;
     forwards: step_not_value Red1; auto; inverts H0
    ];
    try solve[
      destruct F; unfold fill in *; inverts H0;
      forwards: step_not_value Red1; auto; inverts H0
    ];
    try solve[destruct F; unfold fill in *; inverts H3].
    + forwards*: fill_eq H0.
      destruct H1. subst. inverts Typ.
      forwards*: fill_chk H3. inverts H5.
      forwards*: IHRed1 Red1 H4. congruence.
    +  forwards*: fill_eq H0.
      destruct H1. subst. inverts Typ.
      forwards: fill_chk H3. inverts* H5.
    +
     forwards: typing_regular Typ.
     destructs~ H1. 
     destruct F; unfold fill in *; inverts H0;
     try solve[
     inverts H6;
     inverts H10;
     forwards: step_not_value Red1; auto; inverts H0].
    + 
      forwards: typing_regular Typ.
     destructs~ H1. 
     destruct F; unfold fill in *; inverts H0;
     try solve[ inverts H6;
     inverts H10;
     forwards: step_not_value Red1; auto; inverts H0 ].
    +
    forwards: typing_regular Typ.
    destructs~ H1. 
    destruct F; unfold fill in *; inverts H0;
    try solve[ inverts H3;
    inverts H7;
    forwards: step_not_value Red1; auto; inverts H0 ].
    +
    forwards: typing_regular Typ.
     destructs~ H1. 
     destruct F; unfold fill in *; inverts H0;
     try solve[ inverts H4;
     inverts H9;
     forwards: step_not_value Red1; auto; inverts H0 ].
     +
    forwards: typing_regular Typ.
     destructs~ H1. 
     destruct F; unfold fill in *; inverts H0;
     try solve[ inverts H4;
     inverts H9;
     forwards: step_not_value Red1; auto; inverts H0 ].
     +
     forwards ha: typing_regular Typ.
     lets(hb&hc&hd):ha. 
     destruct F; unfold fill in *; inverts H0;
     try solve[ inverts hc;
     inverts H1;
     forwards: step_not_value Red1; auto; inverts H0 ].
  - inverts Red2;
    try solve[destruct F; unfold fill in H0; inverts H0];
    try solve[reflexivity];
    try solve[inverts H3];
    try solve[forwards: step_not_value Red1; auto; inverts H0].
    inverts Typ. inverts H1;
    forwards*: IHRed1 Red1 H4.
    inverts Typ. inverts H1;
    forwards*: IHRed1 Red1 H5;
    inverts H1.
  -
    inverts* Red2; 
    try solve[destruct F; unfold fill in H4; inverts* H4;
    forwards: step_not_value H8; auto; inverts H4];
    try solve[inverts H7].
    +
     forwards*: typing_regular Typ.
     destructs~ H5. 
     destruct F; unfold fill in *; inverts* H4;
     try solve[
     inverts* H7;
     inverts* H11;
     forwards: step_not_value H8; auto; inverts* H0]. 
    +
     forwards*: typing_regular Typ.
     destructs~ H5. 
     destruct F; unfold fill in *; inverts* H4;
     try solve[
     inverts* H7;
     inverts* H11;
     forwards: step_not_value H8; auto; inverts* H0]. 
    +
    inverts Typ. inverts H5. inverts H16. inverts H17.
    forwards: pattern_abs_uniq H2 H14. inverts H7.
    forwards*: TypeLists_unique H3 H15.
    congruence.
    +
    inverts Typ. inverts H5.
    inverts H16. inverts H17. 
    forwards*: pattern_abs_uniq H2 H14. inverts H7.
    forwards*: TypeLists_unique H3 H15.
    congruence.
    +
    inverts H11. inverts* H13.
    exfalso; apply H14; eauto.
    inverts Typ. inverts H5.
    inverts H17. inverts H13.
    lets typ: H6. inverts H6. 
    forwards*: typing_regular typ.
    destructs~ H6.
    inverts* H13.
  -
    inverts* Red2; 
    try solve[destruct F; unfold fill in H4; inverts* H4;
    forwards: step_not_value H8; auto; inverts H4];
    try solve[inverts H7].
    +
    forwards*: typing_regular Typ.
     destructs~ H5. 
     destruct F; unfold fill in *; inverts* H4;
     try solve[
     inverts* H7;
     inverts* H11;
     forwards: step_not_value H8; auto; inverts* H0]. 
    +
    forwards*: typing_regular Typ.
     destructs~ H5. 
     destruct F; unfold fill in *; inverts* H4;
     try solve[
     inverts* H7;
     inverts* H11;
     forwards: step_not_value H8; auto; inverts* H0]. 
    +
    forwards*: pattern_abs_uniq H2 H14. inverts H4.
    inverts Typ. inverts H5. inverts H17.
    forwards*: TypeLists_unique H3 H15.
    congruence.
  -
    inverts* Red2; 
    try solve[destruct F; unfold fill in H3; inverts* H3;
    forwards: step_not_value H7; auto; inverts H3];
    try solve[inverts H6].
    inverts* H1.
    inverts* H11. inverts* H13.
    inverts Typ. inverts H3. inverts H16.
    inverts H13.
    forwards*: typing_regular H4.
    destructs~ H5.
    inverts* H4.
    inverts* H15.
    exfalso; apply H14; eauto.
  -
    inverts Red2;
    try solve[destruct F; unfold fill in H0; inverts H0];
    try solve[reflexivity];
    try solve[inverts H0];
    try solve[forwards: step_not_value Red1; auto; inverts H0].
    forwards*: ptype_uniq H1 H7.
    subst*.
  -
    inverts Red2;
    try solve[destruct F; unfold fill in H0; inverts H0];
    try solve[reflexivity];
    try solve[inverts H3];
    try solve[forwards: step_not_value Red1; auto; inverts H0].
    +
    inverts Typ. inverts H1.
    forwards*: IHRed1 Red1 H4.
    congruence. 
    +
    inverts Typ. inverts H1.
    forwards*: IHRed1 Red1 H5.
    congruence. 
  - 
    inverts Red2;
    try solve[destruct F; unfold fill in H2; inverts H2];
    try solve[reflexivity];
    try solve[inverts H5];
    try solve[forwards: step_not_value H6; auto; inverts H2];
    try solve[forwards: step_not_value H7; auto; inverts H2].
    inverts Typ. inverts H3; try solve[
    forwards*: TypedReduce_unique H1 H8];
    try solve[inverts H10;
    forwards*: TypedReduce_unique H1 H8].
  -
    inverts* Red2; 
    try solve[destruct F; unfold fill in H3; inverts H3];
    try solve[destruct F; unfold fill in *; inverts H3];
    try solve[inverts* H8];
    try solve[inverts* H8];
    try solve[inverts* H4];
    try solve[
      destruct F; unfold fill in *; inverts H3;
      forwards*: step_not_value H7; auto; inverts H; auto].
    +
    forwards*: typing_regular Typ.
     destructs~ H2. 
     destruct F; unfold fill in *; inverts* H1;
     try solve[
     inverts* H4;
     inverts* H;
     forwards: step_not_value H5; auto; inverts* H0].
    +
    forwards*: typing_regular Typ.
     destructs~ H2. 
     destruct F; unfold fill in *; inverts* H1;
     try solve[
      inverts* H4;
      inverts* H8;
      forwards: step_not_value H5; auto; inverts* H0].
    +
      forwards* ha: pattern_all_uniq H0 H8. 
      inverts* ha.
    + inverts* H8.
      exfalso; apply H10.
      inverts H9. 
      inverts Typ. inverts H2. inverts H14. inverts H11.
      lets typ: H3.
      inverts H3.
      forwards*: typing_regular typ.
      destructs~ H3.
      inverts H11.
      pick fresh x and apply consist_all; auto.
  -
    inverts* Red2;
    try solve[destruct F; unfold fill in *; inverts* H3;
    forwards*: step_not_value H7];
    try solve[inverts H5].
    +
     forwards*: typing_regular Typ.
     destructs~ H3. 
     destruct F; unfold fill in *; inverts* H2;
     try solve[
     inverts* H5;
     inverts* H9;
     forwards: step_not_value H6; auto; inverts* H0]. 
    +
    forwards*: typing_regular Typ.
     destructs~ H3. 
     destruct F; unfold fill in *; inverts* H2;
     try solve[
     inverts* H5;
     inverts* H10;
     forwards: step_not_value H6; auto; inverts* H0].
    +
    inverts H8.
    inverts H1.
    inverts H8.
    inverts Typ. inverts H2. inverts H13.
    inverts H10.
    forwards*: typing_regular H3.
    destructs~ H4.
    inverts* H3.
    inverts* H11.
    exfalso; apply H9; eauto.
  - 
    inverts Red2; 
    try solve[destruct F; unfold fill in H1; inverts H1];
    try solve[destruct F; unfold fill in *; inverts H1];
    try solve[inverts* H6];
    try solve[
      destruct F; unfold fill in *; inverts H1;
      forwards: step_not_value H7; auto; inverts H1].
    +
    forwards*: typing_regular Typ.
     destructs~ H4. 
     destruct F; unfold fill in *; inverts* H1;
     try solve[
     inverts* H6;
     inverts* H10;
     forwards: step_not_value H7; auto; inverts* H0]. 
    +
    forwards*: typing_regular Typ.
     destructs~ H4. 
     destruct F; unfold fill in *; inverts* H1;
     try solve[
     inverts* H6;
     inverts* H10;
     forwards: step_not_value H7; auto; inverts* H0].
    +
    forwards: pattern_ref_uniq H3 H12. inverts H1.
    inverts Typ. inverts H4. inverts H15.
    forwards*: TypeLists_unique H2 H11.
    congruence.
    +
    forwards: pattern_ref_uniq H3 H12. inverts H1.
    inverts Typ. inverts H4. inverts H15.
    forwards*: TypeLists_unique H2 H11.
    congruence.
    +
    inverts* H11. inverts H12.
    inverts well. inverts H4.
    exfalso; apply H13; eauto.
    eapply consist_ref; eauto.
    inverts Typ. inverts H11.
    inverts H18. inverts H16. inverts H12.
    rewrite H5 in *.
    forwards*: H8.
    forwards*: typing_regular H12.
    forwards*: sto_ok_value H7.
    forwards*: principle_typ_inf H12.
    rewrite H20; eauto.
  -
    inverts* Red2; 
    try solve[destruct F; unfold fill in H1; inverts H1];
    try solve[destruct F; unfold fill in *; inverts H1];
    try solve[inverts* H6];
    try solve[
      destruct F; unfold fill in *; inverts H1;
      forwards: step_not_value H7; auto; inverts H1].
    +
    forwards*: typing_regular Typ.
     destructs~ H4. 
     destruct F; unfold fill in *; inverts* H1;
     try solve[
     inverts* H6;
     inverts* H10;
     forwards: step_not_value H7; auto; inverts* H0]. 
    +
    forwards*: typing_regular Typ.
    destructs~ H4. 
    destruct F; unfold fill in *; inverts* H1;
    try solve[
    inverts* H6;
    inverts* H10;
    forwards: step_not_value H7; auto; inverts* H0]. 
    +
    inverts Typ. inverts H4.
    forwards*: pattern_ref_uniq H3 H12. inverts H4.
    inverts H15.
    forwards*: TypeLists_unique H2 H11.
    inverts* H6.
  -
    inverts* Red2; 
    try solve[destruct F; unfold fill in H3; inverts H3];
    try solve[destruct F; unfold fill in *; inverts H1];
    try solve[inverts* H6];
    try solve[
      destruct F; unfold fill in *; inverts H3;
      forwards: step_not_value H7; auto; inverts H3].
    inverts H2. 
    inverts Typ. inverts H3. inverts H16.
    inverts H14.
    forwards*: typing_regular H4.
    destructs~ H5.
    exfalso; apply H13.
    forwards*: ptype_inf H4.
    forwards*: ptype_uniq H16 H10.
    inverts* H18.
    inverts* H10.
    inverts* H15.
  -
    inverts* Red2; 
    try solve[destruct F; unfold fill in H0; inverts H0];
    try solve[destruct F; unfold fill in *; inverts H0];
    try solve[inverts* H4];
    try solve[
      destruct F; unfold fill in *; inverts H1;
      forwards: step_not_value H5; auto; inverts H1].
  -
    inverts* Red2; 
    try solve[destruct F; unfold fill in H1; inverts H1];
    try solve[destruct F; unfold fill in *; inverts H1];
    try solve[inverts* H6];
    try solve[
      destruct F; unfold fill in *; inverts H1;
      forwards: step_not_value H5; auto; inverts H0].
    + 
    forwards*: typing_regular Typ.
     destructs~ H2. 
     destruct F; unfold fill in *; inverts* H1;
     try solve[
     inverts* H4;
     inverts* H7;
     forwards: step_not_value H5; auto; inverts* H0].
    +
    forwards*: typing_regular Typ.
     destructs~ H2. 
     destruct F; unfold fill in *; inverts* H1;
     try solve[
     inverts* H4;
     inverts* H7;
     forwards: step_not_value H5; auto; inverts* H0].
     +
     inverts Typ. inverts H2.
    forwards*: pattern_ref_uniq H0 H6. inverts H2; auto.
    +
    inverts H7. exfalso; apply H10.
    inverts Typ. inverts H2.
    inverts H12. inverts H11. inverts H3.
    forwards*: consist_regular H2.
    destructs~ H3. inverts H8.
    inverts H9.
    inverts well. inverts H9.
    rewrite H14 in *.
    forwards*: H16.
    forwards*: principle_typ_inf H9.
    forwards*: sto_ok_value H4.
    rewrite H18; eauto.
  -
    inverts* Red2; 
    try solve[destruct F; unfold fill in H2; inverts H2];
    try solve[destruct F; unfold fill in *; inverts H2];
    try solve[inverts* H5];
    try solve[
      destruct F; unfold fill in *; inverts H2;
      forwards: step_not_value H6; auto; inverts H2].
    inverts H1.
    inverts Typ. inverts H2.
    inverts H12. inverts H11.
    forwards*: typing_regular H3.
    destructs~ H8.
    forwards*: ptype_inf H3.
    forwards*: ptype_uniq H9 H13. subst.
    exfalso; apply H10.
    inverts* H13.
    eapply consist_ref; eauto.
    inverts* H12.
Qed.

  


