Require Export Metalib.Metatheory.
Require Import LibTactics.

Require Import Definitions.
Require Import Infrastructure.
Require Import Lemmas.
Require Import Lia.


(* ********************************************************************** *)
(** Weakening (5) *)


Lemma typing_weakening : forall E F G P e T dir,
   typing (E ++ G) P e dir T ->
   wf_env (E ++ F ++ G) ->
   typing (E ++ F ++ G) P e dir T.
Proof with simpl_env;
eauto using 
            wf_typ_from_wf_env_typ,
            wf_typ_weakening,
            consist_weakening.
 introv Typ. gen F. 
 inductions Typ; introv Ok; eauto.
 - forwards*:  wf_typ_weakening H1.
 - pick fresh x and apply typ_abs.
   lapply (H x); [intros K | auto].
    rewrite <- app_assoc.
    apply (H0 x)...
  - apply typ_tabs with (L := ((((((((L \u fv_ee e) \u fv_tt A) \u dom E) \u dom G) \u dom F) \u
    fv_tt_env E) \u fv_tt_env G) \u fv_tt_env F) );intros.
    lapply (H a); [intros K | auto].
    rewrite <- app_assoc.
    apply (H0 a)...
  - eapply typ_tapp with (A1:= A1); eauto.
    apply* wf_typ_weakening.
  -
    apply* typ_consist.
    apply* consist_weakening.
Qed.


Lemma fv_in_dom: forall G P e dir T,
    typing G P e dir T -> fv_ee e [<=] dom G.
Proof.
  intros G P e dir T H.
  inductions H; simpl; try fsetdec.
  -
    apply binds_In in H0.
    fsetdec.
  -
    pick fresh x for (L \u dom (E) \u fv_ee e).
    assert (Fx : fv_ee (e open_ee_var x) [<=] dom (x ~: A ++ E)).
    { forwards*: H0 x. }
    simpl in Fx.
    assert (Fy : fv_ee e [<=] fv_ee (e open_ee_var x)) by
        eapply fv_ee_open_ee_lower.
    fsetdec.
  - 
    pick fresh x for (L \u dom (E) \u fv_ee e).
    assert (Fx : fv_ee (open_te e (t_fvar x)) [<=] dom (x ~tvar ++ E)).
    { forwards*: H0 x. }
    simpl in Fx.
    assert (Fy : fv_ee e [<=] fv_ee (open_te e (t_fvar x))).
    eapply fv_ee_open_te_lower.
    fsetdec.
Qed.


Lemma tfv_in_dom_wft: forall E A,
 wf_typ E A ->
 fv_tt A [<=] dom E.
Proof.
  introv wf.
  inductions wf; simpl; try fsetdec.
  -
  apply binds_In in H.
    fsetdec.
  -
  pick fresh x for (L \u dom (E) \u fv_tt A).
  assert (Fx : fv_tt (open_tt A (t_fvar x)) [<=] dom (x ~tvar ++ E)).
  { forwards*: H0 x. }
  simpl in Fx.
  assert (Fy : fv_tt A [<=] fv_tt (open_tt A (t_fvar x))).
  eapply fv_tt_open_tt_lower.
  fsetdec.
Qed.



Lemma value_no_fv : forall P v dir T,
    typing nil P v dir T -> fv_ee v [<=] {}.
Proof.
  introv Typ.
  pose proof (fv_in_dom nil P v).
  intuition eauto.
Qed.



Lemma value_no_tfv : forall P v dir T,
    typing nil P v dir T -> fv_tt T [<=] {}.
Proof.
  introv Typ.
  forwards*:typing_regular Typ.
  inverts H. inverts H1.
  forwards*: tfv_in_dom_wft H2.
Qed.


Lemma subst_value : forall P v T dir z u,
    typing nil P v dir T -> subst_ee u z v = v.
Proof.
  intros P v dir T z u Typ.
  lets* Fv: value_no_fv Typ.
  forwards*: subst_ee_fresh.
  rewrite Fv.
  fsetdec.
Qed.


Lemma subst_value_ty : forall P v T dir z u,
    typing nil P v dir T -> subst_tt u z T = T.
Proof.
  intros P v dir T z u Typ.
  lets* Fv: value_no_tfv Typ.
  forwards*: subst_tt_fresh.
  rewrite Fv.
  fsetdec.
Qed.


Lemma length_less: forall l n,
 l < S n ->
 l = n \/ l < n.
Proof.
  introv les.
  inverts* les.
Qed.


Lemma nth_eq_last : forall A (l:list A) x d,
  nth (length l) (l ++ x::nil) d = x.
Proof.
  induction l; intros; [ auto | simpl; rewrite IHl; auto ].
Qed.


Lemma sto_ok_value: forall l mu,
 l < length mu ->
 sto_ok mu ->
 value ((store_lookup l mu)).
Proof.
  introv len ok. gen l.
  inductions ok; intros; try solve[inverts len];
  simpl in *.
  destruct l; simpl; eauto.
  forwards*: IHok l.
  lia.
Qed.



Lemma principle_typ_inf: forall P u A,
 value u -> 
 typing empty P u Inf A -> 
 principle_type u = A.
Proof.
  introv val typ.
  inverts* val; try solve[inverts* typ].
Qed.



Lemma inference_unique : forall G P e A1 A2,
    typing G P e Inf A1 ->
    typing G P e Inf A2 ->
    A1 = A2.
Proof.
  introv Ty1.
  gen_eq Dir : Inf.
  gen A2.
  induction Ty1; introv Eq Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    forwards*: binds_unique H0 H5. inverts* H1.
  - (* t_app *)
    forwards * : IHTy1_1 H5.
    inverts* H0. inverts* H;inverts* H2.
  - (* t_all *)
    forwards * : IHTy1 H7.
    inverts* H1. inverts* H0; inverts* H6.
  - forwards * : IHTy1 H2.
    inverts* H.
  - forwards * : IHTy1 H4.
    inverts* H0. inverts H;inverts* H1.
Qed.



(************************************************************************ *)
(** ** Substitution preserves typing (8) *)

Lemma typing_through_subst_ee : forall P U E F x dir T e u,
  typing (F ++ x ~ bind_typ U ++ E) P e dir T ->
  typing E P u Inf U ->
  typing (F ++ E) P (subst_ee x u e) dir T.
Proof with simpl_env;
           eauto 4 using wf_typ_strengthening,
                         wf_env_strengthening,
                         consist_strengthening.
Proof.
  introv TypT TypU.
  remember (F ++ x ~ bind_typ U ++ E) as E'.
  generalize dependent F.
  inductions TypT; intros F EQ; subst; simpl subst_ee...
  -
    destruct (x0 == x); try subst x0.
    +
    analyze_binds_uniq H0.
    injection BindsTacVal; intros; subst.
    rewrite_env (empty ++ F ++ E).
    apply typing_weakening...
    +
    analyze_binds H0.
    eauto using wf_env_strengthening.
    eauto using wf_env_strengthening.
  -
    pick fresh y and apply typ_abs.
    rewrite subst_ee_open_ee_var...
    rewrite <- app_assoc.
    apply H0...
  -
    pick fresh y.
    apply typ_tabs with (L := (((((((((((L \u singleton x) \u fv_te u) \u fv_te e) \u fv_ee u) \u fv_ee e) \u
    fv_tt U) \u fv_tt A) \u dom E) \u dom F) \u 
    fv_tt_env E) \u fv_tt_env F));intros.
    rewrite subst_ee_open_te_var...
    rewrite <- app_assoc.
    apply H0...
Qed.



Lemma consist_through_subst_tt : forall E F Y S T A,
  consist (F ++ Y ~tvar ++ E) S T ->
  wf_typ E A ->
  consist (map (subst_tb Y A) F ++ E) (subst_tt Y A S) (subst_tt Y A T).
Proof with simpl_env;
     eauto 4 using wf_typ_subst_tb, wf_env_subst_tb, wf_typ_weaken_head.
  introv SsubT PsubQ.
  remember (F ++ Y ~tvar ++ E) as G.
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl subst_tt...
  -
    destruct (x == Y); subst.
    apply consist_refl...
    apply consist_refl...
    inverts* H0.
    analyze_binds H3...
    apply* wf_typ_var.
    assert (bind_tvar = subst_tb Y A bind_tvar).
    reflexivity. rewrite H0.
    assert(binds x (subst_tb Y A bind_tvar) (map (subst_tb Y A) G)).
    forwards: binds_map_2 BindsTac.
    apply H1.
    forwards: binds_app_2 H1.
    apply H2.
  -
    apply consist_dyn_l...
  -
    apply consist_dyn_r...
  -
    pick fresh X and apply consist_all...
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Y A) (X ~tvar ++ G) ++ E).
    apply H0...
Qed.



Lemma typing_through_subst_te : forall E F Z ph e T P mu dir,
  ph |== mu ->
  typing (F ++ Z~tvar ++ E) ph e dir T ->
  wf_typ E P ->
  typing (map (subst_tb Z P) F ++ E) ph (subst_te Z P e) dir (subst_tt Z P T).
Proof with simpl_env;
           eauto 6 using wf_env_subst_tb,
                         wf_typ_subst_tb,
                         consist_through_subst_tt.
 introv wel TypT TypU.
 remember (F ++ Z~tvar ++ E) as E'.
 generalize dependent F.
 inductions TypT; intros F EQ; subst; simpl subst_te; simpl subst_tt;
 try solve[inverts* H]...
 -
   apply typ_var...
   rewrite (map_subst_tb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
   analyze_binds H0...
   forwards*: wf_env_subst_tb H TypU.
   forwards*: wf_env_concat_left_inv H1.
  -
    forwards*: wf_env_subst_tb H TypU.
    forwards*: wf_typ_subst_tb H1 TypU.
    inverts wel. inverts H5.
    rewrite H6 in H0.
    forwards*: H7 H0.
    forwards*:subst_value_ty H5.
    rewrite <- H6 in H0.
    rewrite H8 in *.
    apply typ_loc; eauto.
  -
    pick fresh y and apply typ_abs.
    rewrite subst_te_open_ee_var...
    rewrite_env (map (subst_tb Z P) (y ~ bind_typ A ++ F) ++ E).
    apply H0... 
  -
    pick fresh X.
    apply typ_tabs with (L := (union L
    (union (singleton Z)
       (union (fv_te e)
          (union (singleton Z)
             (union (fv_ee e)
                (union (singleton Z)
                   (union (fv_tt P)
                      (union (fv_tt A)
                         (union (dom E)
                            (union (dom F)
                               (union (fv_tt_env E) (fv_tt_env F)))))))))))) );intros.
    rewrite subst_te_open_te_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) (a ~tvar ++ F) ++ E).
    apply H0...
  -
     rewrite subst_tt_open_tt...
    forwards*: IHTypT.
    inverts H0; simpl in *; eauto.
    eapply typ_tapp...
    eapply typ_tapp ...
Qed.


Lemma typing_subst_simpl_ee : forall P U E x T e u dir,
  typing (x ~ bind_typ U ++ E) P e dir T ->
  typing E P u Inf U ->
  typing E P (subst_ee x u e) dir T.
Proof.
    introv typ1 typ2.
    rewrite_env (nil++E).
    apply* typing_through_subst_ee.
Qed.


Lemma consist_subst_simpl : forall E Y S T A,
  consist (Y ~tvar ++ E) S T ->
  wf_typ E A ->
  consist (E) (subst_tt Y A S) (subst_tt Y A T).
Proof.
  introv con type.
  rewrite_env (map (subst_tb Y A) empty ++E).
  apply* consist_through_subst_tt.
Qed.


Lemma typing_subst_simpl_te : forall ph mu E Z e T P dir,
  ph |== mu ->
  typing (Z~tvar ++ E) ph e dir T ->
  wf_typ E P ->
  typing (E) ph (subst_te Z P e) dir (subst_tt Z P T).
Proof.
  introv wel typ1 typ2.
  rewrite_env (map (subst_tb Z P) empty ++E).
  apply* typing_through_subst_te.
Qed.



Lemma extends_lookup : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  store_Tlookup l ST' = store_Tlookup l ST.
Proof with auto.
  intros l ST.
  generalize dependent l.
  induction ST as [|a ST2]; intros l ST' Hlen HST'.
  - (* nil *) inversion Hlen.
  - (* cons *) unfold store_Tlookup in *.
    destruct ST'.
    + (* ST' = nil *) inversion HST'.
    + (* ST' = a' :: ST'2 *)
      inversion HST'; subst.
      destruct l as [|l'].
      * (* l = 0 *) auto.
      * (* l = S l' *) simpl. apply IHST2...
        simpl in Hlen; lia.
Qed.


Lemma extends_refl : forall E,
  extends E E.
Proof. 
 intros_all~.
 inductions E; eauto. 
Qed.


Lemma length_extends : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  l < length ST'.
Proof with eauto.
  intros. generalize dependent l. induction H0; intros l Hlen.
    - inversion Hlen.
    - simpl in *.
      destruct l; try lia.
        apply lt_n_S. apply IHextends. lia.
Qed.


Lemma extends_wf_typ: forall l P1 P2 E,
 l < length P1 ->
 extends P2 P1 ->
 wf_typ E (store_Tlookup l P1) ->
 wf_typ E (store_Tlookup l P2).
Proof.
  introv len ext wf. gen l E.
  inductions ext; intros; eauto;
  try solve[inverts len]; simpl in *.
  destruct l; simpl; eauto.
  forwards*: IHext l E. lia.
Qed.




Lemma store_weakening : forall G ST ST' t dir T,
  extends ST' ST ->
  typing G ST t dir T ->
  typing G ST' t dir T.
Proof with eauto.
  intros. induction H0; eauto.
  - (* T_Loc *)
    rewrite <- (extends_lookup _ _ ST')...
    apply typ_loc; eauto.
    eapply length_extends...
    forwards*: extends_wf_typ H2.
Qed.


Lemma extends_app : forall ST T,
  extends (ST ++ T) ST.
Proof.
  induction ST; intros T.
  auto.
  simpl. auto.
Qed.


Hint Resolve extends_refl extends_app store_weakening: core.



(* ********************************************************************** *)
(** ** Preservation *)


Lemma ptype_uniq: forall mu u A B,
 sto_ok mu -> pvalue u -> ptype mu u A -> ptype mu u B -> A = B.
Proof.
  introv sto pval ptyp1 ptyp2.
  inductions pval; try solve[inverts* ptyp1; inverts* ptyp2].
Qed.


Lemma ptype_inf: forall mu P u A,
 P |== mu ->
 pvalue u -> 
 typing empty P u Inf A -> 
 ptype mu u A.
Proof.
  introv sto pval typ.
  inverts* typ; try solve[inverts* pval].
  inverts sto. inverts H3.
  rewrite H4 in H0. 
  forwards*: H5 H0.
  forwards*: sto_ok_value H0 H2. 
  forwards*: principle_typ_inf H3.
Qed.


Lemma TypedReduce_preservation: forall P mu v A v' B,
      P |== mu ->
     value v -> 
     TypedReduce (v, mu) A ((r_e v'),mu) -> 
     typing nil P v Chk B -> typing nil P v' Inf A.
Proof with auto.
  introv well val red typ.
  inductions red; eauto.
  -
    inverts typ. inverts H3.
    + inverts H7.
      forwards*: ptype_inf H4. 
      forwards*: ptype_uniq H0 H5.
      inverts* well.
      subst*.
Qed.


Lemma TypedReduce_prv_value: forall v A v' mu,
    value v -> 
    type A ->
    TypedReduce (v, mu) A ((r_e v'), mu) -> value v'.
Proof.
  introv Val type Red.
  inductions Red; eauto.
Qed.


Lemma TypeLists_prv_value: forall v A v' B mu,
 value v -> 
 type A ->
 type B ->
 TypeLists (v,mu) (A :: B :: nil)%list ((r_e v'), mu) 
     ->  value v'.
Proof with auto.
 introv val ty1 ty2 tlist.
 inverts tlist. 
 inverts* H5. inverts* H7. 
 forwards*: TypedReduce_prv_value H2.
 forwards*: TypedReduce_prv_value H3.
Qed.


Lemma TypeLists_preservation: forall v A0 A v' B mu P,
 P |== mu ->
 type A ->
 type B ->
 value v -> TypeLists (v,mu) (A :: B :: nil)%list ((r_e v'), mu) 
     -> typing nil P v Chk A0 -> typing nil P v' Inf B.
Proof with auto.
 introv well ty1 ty2 val tlist typ.
 inverts tlist. 
 inverts* H5. inverts* H7. 
 forwards*: TypedReduce_prv_value H2.
 forwards*: TypedReduce_preservation H2.
 forwards*: TypedReduce_prv_value H3.
 forwards*: TypedReduce_preservation H3.
Qed.


Lemma sto_ok_app: forall st1 st2,
 sto_ok st1 ->
 sto_ok st2 ->
 sto_ok (st1 ++ st2).
Proof.
  introv ok1 ok2.
  inductions ok1; simpl; eauto.
Qed.



Lemma TypeLists3_preservation: forall v A0 A v' B mu P,
 P |== mu ->
 type A ->
 type B ->
 value v -> TypeLists (v,mu) (A :: t_dyn :: B :: nil)%list ((r_e v'), mu) 
     -> typing nil P v Chk A0 -> typing nil P v' Inf B.
Proof with auto.
 introv well ty1 ty2 val tlist typ.
 inverts tlist. 
 inverts* H5. inverts* H7. inverts H8. 
 forwards*: TypedReduce_prv_value H2.
 forwards*: TypedReduce_preservation H2.
 forwards*: TypedReduce_prv_value H3.
 forwards*: TypedReduce_preservation H3.
 forwards*: TypedReduce_prv_value H4.
 forwards*: TypedReduce_preservation H4.
Qed.


Lemma TypeLists2_preservation: forall v A0 A v' B mu P,
 P |== mu ->
 type A ->
 type B ->
 value v -> TypeLists (v,mu) (A :: B :: nil)%list ((r_e v'), mu) 
     -> typing nil P v Chk A0 -> typing nil P v' Inf B.
Proof with auto.
 introv well ty1 ty2 val tlist typ.
 inverts tlist. 
 inverts* H5. inverts* H7. 
 forwards*: TypedReduce_prv_value H2.
 forwards*: TypedReduce_preservation H2.
 forwards*: TypedReduce_prv_value H3.
 forwards*: TypedReduce_preservation H3.
Qed.


Lemma add_sym : forall m,
 1 + m = m + 1.
Proof.
  introv. 
  inductions m; intros; eauto.
  simpl.
  rewrite <- IHm.
  simpl.
  reflexivity.
Qed.


Lemma store_well_typed_app : forall ST st t1 T1,
  value t1 ->
  sto_typing ST st ->
  typing nil  ST t1 Inf T1 ->
  sto_typing (ST ++ T1::nil) (st ++ t1::nil).
Proof with auto.
  intros.
  unfold sto_typing in *.
  destruct H0. destruct H2. 
  rewrite app_length. simpl.
  rewrite app_length. simpl.
  split;eauto.
  - apply sto_ok_app;eauto.
  - (* types match. *)
    split;eauto.
    intros l Hl.
    unfold store_lookup, store_Tlookup.
    apply le_lt_eq_dec in Hl; destruct Hl as [Hlt | Heq].
    + (* l < length st *)
      rewrite !app_nth1; try solve[lia].
      * apply store_weakening with ST. apply extends_app.
        forwards*: H3. lia.
    + (* l = length st *)
      assert(1 + length st = S (length st)).
      simpl;eauto.
      rewrite add_sym in H4.
      rewrite H4 in *.
      injection Heq as Heq; subst.
      rewrite app_nth2; try lia.
      rewrite <- H2.
      rewrite minus_diag. simpl.
      apply store_weakening with ST...
      rewrite app_nth2; [|lia].
      rewrite minus_diag. simpl. assumption.
Qed.


Lemma length_replace : forall A n x (l:list A),
  length (replace n x l) = length l.
Proof with auto.
  intros A n x l. generalize dependent n.
  induction l; intros n.
    destruct n...
    destruct n...
      simpl. rewrite IHl...
Qed.


Lemma lookup_replace_eq : forall l t st,
  l < length st ->
  store_lookup l (replace l t st) = t.
Proof with auto.
  intros l t st.
  unfold store_lookup.
  generalize dependent l.
  induction st as [|t' st']; intros l Hlen.
  - (* st =  *)
   inversion Hlen.
  - (* st = t' :: st' *)
    destruct l; simpl...
    apply IHst'. simpl in Hlen. lia.
Qed.


Lemma replace_nil : forall A n (x:A),
  replace n x nil = nil.
Proof.
  destruct n; auto.
Qed.



Lemma lookup_replace_neq : forall l1 l2 t st,
  l1 <> l2 ->
  store_lookup l1 (replace l2 t st) = store_lookup l1 st.
Proof with auto.
  unfold store_lookup.
  induction l1 as [|l1']; intros l2 t st Hneq.
  - (* l1 = 0 *)
    destruct st.
    + (* st =  *) rewrite replace_nil...
    + (* st = _ :: _ *) destruct l2... contradict Hneq...
  - (* l1 = S l1' *)
    destruct st as [|t2 st2].
    + (* st =  *) destruct l2...
    + (* st = t2 :: st2 *)
      destruct l2...
      simpl; apply IHl1'...
Qed.


Lemma replace_sto_ok : forall l v st,
 l < length st ->
 value v ->
 sto_ok st ->
 sto_ok (replace l v st).
Proof.
  introv len val ok. gen l v.
  inductions ok; intros;
  try solve[inverts len];
  simpl in *.
  destruct l; simpl; eauto.
  apply sto_ok_push; auto.
  forwards*: IHok l val. lia.
Qed. 


Lemma assign_pres_store_typing : forall ST st l t,
  l < length st ->
  value t ->
  sto_typing ST st ->
  typing nil ST t Inf (store_Tlookup l ST) ->
  sto_typing ST (replace l t st).
Proof with auto.
  introv  Hlen val HST Ht.
  inverts HST. inverts H0.
  unfold sto_typing.
  split.
  forwards*: replace_sto_ok Hlen val.
  split.
  rewrite length_replace...
  intros l' Hl'.
  destruct (l' == l).
  - (* l' = l *)
    inverts e.
    rewrite lookup_replace_eq...
  - (* l' <> l *)
    rewrite lookup_replace_neq...
    rewrite length_replace in Hl'.
    apply H2...
Qed.


Theorem preservation : forall P mu mu' e e' dir T,
  P |== mu ->
  typing nil P e dir T ->
  step (e,mu) ((r_e e'), mu') ->
  exists P', 
  extends P' P /\ 
  typing nil P' e' dir T /\
  P' |== mu'.
Proof with eauto.
  introv well Typ Red. lets Typ': Typ. gen mu mu' e'.
  inductions Typ; introv well Red.
  - (* var *)
    inverts* Red; try solve[destruct F in H1; unfold fill in H1; inverts* H1];
    try solve[inverts* H6].
  - (* lit *)
    inverts* Red; try solve[destruct F in H0; unfold fill in H0; inverts* H0];
    try solve[inverts* H6].
    inverts* H6.
    exists* P; split*.
  -
    inverts* Red; 
    try solve[destruct F in H0; unfold fill in H0; 
    inverts* H0].
    inverts* H6.
    exists* P.
  -
    inverts* Red; 
    try solve[destruct F in H2; unfold fill in H2; 
    inverts* H2].
    exists* P; split*. split*.
    inverts well. inverts H3.
    rewrite H4 in H0.    
    forwards*: H5 H0.
    forwards*: sto_ok_value H6.
    forwards*: principle_typ_inf H3.
    inverts H8.
    rewrite H10.
    apply typ_anno; eauto.
  - (* app *)
    inverts Red; try solve[inverts* H5].
    +
      destruct F; unfold fill in H0; inverts* H0; simpl in *.
      forwards*: IHTyp1 H5.
      inverts* H0. 
      exists* x.
      forwards*: IHTyp2 H5.
      inverts* H0.
      exists* x.
    + inverts Typ1.
      inverts H7.
      inverts H3. inverts H1. 
      inverts H8; inverts H.
      forwards*: TypeLists2_preservation H9.
      inverts H0.
      exists* P. split*. split*.
      apply~ typ_anno.
      apply typ_consist with (A := B1); eauto.
      apply~ typ_anno.
      pick_fresh x.
      rewrite* (@subst_ee_intro x).
      apply* typing_subst_simpl_ee.
      forwards*: TypeLists2_preservation H9.
      inverts H0. inverts H2.
      exists* P. split*. split*.
      apply~ typ_anno.
      apply typ_consist with (A := B1); eauto.
      apply~ typ_anno.
      pick_fresh x.
      rewrite* (@subst_ee_intro x).
      apply* typing_subst_simpl_ee.
  - (* abs *)
    inverts* Red; try solve[destruct F in H1; unfold fill in H1; inverts* H1].
    inverts* H7.
    exists* P.
  - (* anno *)
    inverts* Red; try solve[destruct F in H; unfold fill in H; inverts* H];
    try solve[inverts* H4].
    +
      forwards*: IHTyp H5.
      inverts* H.
    +
      forwards*: typing_regular Typ.
     forwards*: TypedReduce_preservation H6.   
  - (* tabs *)
    inverts* Red;try solve[destruct F; unfold fill in H1; inverts* H1].
    inverts* H7.
    exists* P.
  - (* tapp *)
    inverts* Red; try solve[inverts* H6].
    +
    destruct F; unfold fill in H1; inverts* H1; simpl in *.
    forwards*: IHTyp H6.
    inverts* H1.
    +
    inverts Typ. inverts* H5. inverts* H2.
    inverts H3. inverts H5. inverts H6. 
    inverts H7; inverts H1; inverts H0.
    *
    exists P. split*. split*.
    eapply typ_anno; eauto.
    apply typ_consist with (A := (open_tt A0 A)); eauto.
    pick_fresh Y.
    rewrite* (@subst_tt_intro Y).
    assert( (open_tt B A) = (subst_tt Y A (B open_tt_var Y))).
    rewrite* (@subst_tt_intro Y).
    rewrite H0.
    apply* consist_subst_simpl.
    eapply typ_anno; eauto.
    pick_fresh X.
    rewrite* (@subst_te_intro X).
    rewrite* (@subst_tt_intro X).
    apply* typing_subst_simpl_te.
    *
    exists P. split*. split*.
    eapply typ_anno; eauto.
    apply typ_consist with (A := (open_tt A0 A)); eauto.
    forwards*: wf_typ_open A H5.
    eapply typ_anno; eauto.
    pick_fresh X.
    rewrite* (@subst_te_intro X).
    rewrite* (@subst_tt_intro X).
    apply* typing_subst_simpl_te.
  - forwards*: IHTyp Red.
    lets(P'&extend&rtyp&rwell): H0.
    exists* P'.
  - 
    inverts* Red; try solve[destruct F in H; unfold fill in H; inverts* H];
    try solve[inverts* H4].
    destruct F; unfold fill in H; simpl in *;inverts* H.
    forwards*: IHTyp H4.
    lets(P'&extend&rtyp&rwell): H.
    exists* P'. 
    lets well': well.
    inverts well. inverts H0.
    exists*(P++A::nil).
    split*.
    split*.
    replace (t_ref A)
    with (t_ref (store_Tlookup (length mu) (P ++ A :: nil))).
    apply typ_loc; eauto.
    rewrite <- H1.
    rewrite app_length. simpl. lia.
    unfold store_Tlookup.
    rewrite <- H1.
    rewrite nth_eq_last; eauto.
    unfold store_Tlookup.
    rewrite <- H1.
    rewrite nth_eq_last; eauto.
    apply store_well_typed_app; assumption.
  - inverts* Red;
    try solve[inverts* H5].
    +
    destruct F; unfold fill in H0; simpl in *;inverts* H0.
    forwards*: IHTyp H5.
    lets(P'&extend&rtyp&rwell): H0.
    exists* P'.
    +
    inverts* Typ. inverts H4. 
    inverts H1. inverts H5;
    inverts H. inverts H0.
    exists* P. split*. split*.
    apply typ_anno; eauto.
    inverts well. inverts H0.
    rewrite H1 in H6.
    forwards*: H2 H6.
    exists* P. split*. split*.
    apply typ_anno; eauto.
    inverts well. inverts H1.
    rewrite H2 in H6.
    forwards*: H5 H6.
  - 
    inverts* Red;
    try solve[inverts* H5].
    +
    destruct F; unfold fill in H0; simpl in *;inverts* H0.
    forwards*: IHTyp1 H5.
    lets(P'&extend&rtyp&rwell): H0.
    exists* P'.
    forwards*: IHTyp2 H5.
    lets(P'&extend&rtyp&rwell): H0.
    inverts H3.
    exists* P'.
    +
    inverts Typ1. inverts H3. inverts H1.
    lets well':well.
    inverts well. inverts H2.
    rewrite H7 in H4.
    forwards*: H10 H4. 
    exists P. split*. split*.
    forwards*: length_replace l0 v2' mu.
    forwards*: typing_regular Typ2.
    forwards*: principle_typ_inf H2.
    forwards*: sto_ok_value l0 H5.
    rewrite <- H14 in H11.
    forwards*: type_from_wf_typ A.
    forwards*: type_from_wf_typ H11.
    inverts H9; inverts* H.
    --
    inverts H15. inverts H0.
    forwards: TypeLists_preservation well' H9 H16 H8; auto.
    apply Typ2.
    rewrite H14 in H.
    forwards*: assign_pres_store_typing H.
    forwards*: TypeLists_prv_value H8.
    --
    forwards: TypeLists_preservation well' H15 H16 H8; auto.
    apply Typ2.
    rewrite H14 in H.
    forwards*: assign_pres_store_typing H.
    forwards*: TypeLists_prv_value H8.
Qed.


(* ********************************************************************** *)
(** ** Progress (16) *)

Lemma FL_decidable:forall A,
 FL A \/ not(FL A).
Proof.
  introv.
  inductions A; try solve[right;unfold not;intros nt; inverts* nt];
  try solve[left*].
Qed.


Lemma pvalue_ss_s: forall u,
 pvalue u -> ssvalue u \/ svalue u.
Proof.
  introv pval.
  inductions pval; eauto.
Qed.



Lemma TypedReduce_progress: forall P v B A mu,
   P |== mu ->
   wf_typ empty A ->
    value v -> typing nil P v Inf B -> 
    exists r, TypedReduce (v,mu) A (r, mu).
Proof.
  introv well ty Val Typ. 
  inverts Val. inverts Typ.
  - inverts H4.
    forwards*: ptype_inf H2.
    destruct(consist_decidable nil A0 A); eauto.
    inverts* H4.
Qed.


Lemma Typelist3_progress: forall P v B A mu,
    P |== mu ->
    wf_typ empty A ->
    wf_typ empty B ->
    value v -> typing nil P v Chk A -> 
    exists r, TypeLists (v,mu) (A :: t_dyn :: B :: nil)%list (r,mu).
Proof.
  introv well ty1 ty2 Val Typ.
  inverts Typ.
  forwards*: TypedReduce_progress A Val H0. inverts H1.
  destruct x; eauto.
  forwards*: TypedReduce_preservation H2.
  forwards*: TypedReduce_prv_value H2.
  forwards*: TypedReduce_progress t_dyn H1. inverts H4.
  destruct x; eauto.
  forwards*: TypedReduce_preservation H5.
  forwards*: TypedReduce_prv_value H5.
  forwards*: TypedReduce_progress B H6 H4. inverts H7.
  destruct x; eauto.
Qed. 



Lemma Typelist_progress: forall P v B0 B A mu,
    P |== mu ->
    wf_typ empty A ->
    wf_typ empty B ->
    value v -> typing nil P v Inf B0 -> 
    exists r, TypeLists (v,mu) (A :: B :: nil)%list (r, mu).
Proof.
  introv well ty1 ty2 Val Typ.
  forwards*: TypedReduce_progress A Val Typ. inverts H.
  destruct x; eauto.
  forwards*: TypedReduce_preservation H0.
  forwards*: TypedReduce_prv_value H0.
  forwards*: TypedReduce_progress B H1 H. inverts H2.
  destruct x; eauto.
Qed. 


Lemma fill_appl : forall e1 e2,
  (e_app e1 e2) = (fill (appCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma fill_appr : forall e1 e2,
  (e_app e1 e2) = (fill (appCtxR e1) e2).
Proof.
  intros. eauto.
Qed.


Lemma fill_setl : forall e1 e2,
  (e_set e1 e2) = (fill (setCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma fill_setr : forall e1 e2,
  (e_set e1 e2) = (fill (setCtxR e1) e2).
Proof.
  intros. eauto.
Qed.

Lemma fill_ref : forall e,
  (e_ref e) = (fill (refCtx) e).
Proof.
  intros. eauto.
Qed.


Lemma fill_get : forall e,
  (e_get e) = (fill (getCtx) e).
Proof.
  intros. eauto.
Qed.

Lemma fill_tapp : forall e1 A,
  (e_tapp e1 A) = (fill (tappCtx A) e1).
Proof.
  intros. eauto.
Qed.


Lemma pvalue_decidable: forall e,
 expr e -> pvalue e \/ not (pvalue e).
Proof.
  introv exp.
  inductions exp; try 
  solve[right; unfold not; intros nt; inverts* nt];
  try solve[left*].
Qed.


Lemma value_decidable: forall e,
 expr e -> value e \/ not (value e).
Proof.
  introv exp.
  inductions exp; try 
  solve[right; unfold not; intros nt; inverts* nt].
  forwards*: pvalue_decidable exp.
  inverts* H0; try 
  solve[right; unfold not; intros nt; inverts* nt].
Qed.



Lemma pattern_type_abs: forall A B,
 type A ->
 pattern_abs A B -> 
 type B.
Proof.
  introv ty pa.
  inverts* pa; eauto.
Qed.

Lemma pattern_type_all: forall A B,
 type A ->
 pattern_all A B -> 
 type B.
Proof.
  introv ty pa.
  inverts pa.
  inverts ty.
  pick fresh x and apply type_all; eauto.
  pick fresh x and apply type_all; eauto.
Qed.

Lemma pattern_type_ref: forall A B,
 type A ->
 pattern_ref A B -> 
 type B.
Proof.
  introv ty pa.
  inverts* pa; eauto.
Qed.

Lemma progress : forall P mu e dir T,
  P |== mu ->
  typing nil P e dir T ->
  value e \/ exists r mu', step (e, mu) (r, mu').
Proof.
  introv wel Typ.
  lets Typ': Typ.
  inductions Typ;
    try solve [left*];
    try solve [right*];
    try solve [inverts* wel];
    try solve [inverts* H0]; eauto. 
  -
    right. 
    lets* [Val1 | [e1' Red1]]: IHTyp1.
    lets* [Val2 | [e2' Red2]]: IHTyp2.
    +
    inverts Val1. inverts Typ1.
    inverts H5.
    forwards*: ptype_inf H3.
    destruct(consist_decidable empty A0 (t_arrow t_dyn t_dyn)); eauto.
    inverts H5.
    *
    inverts* H0; try solve[inverts* H4;inverts* H7].
    forwards*: typing_regular H3. destructs~ H0.
    inverts H3. inverts H9.
    forwards*: pattern_type_abs H.
    lets wel': wel.
    inverts wel.
    forwards*: typing_regular Typ2. destructs~ H11.
    inverts Typ2.
    forwards*: Typelist_progress wel' H15 H12 H18.
    inverts H19.
    destruct x; eauto. 
    *
    inverts H; inverts H2;
    try solve[exfalso; apply H7; eauto].
    inverts wel.
    exists*.  
    +
    inverts* Red2.
    rewrite fill_appr.  destruct e2'; exists*.
    +
    inverts* Red1.
    rewrite fill_appl. destruct e1'; exists*.
  -
    right. 
    inverts wel.
    forwards*: typing_regular Typ'.
    exists*.
  -
    forwards*: IHTyp Typ. inverts H.
    +
    inverts Typ.
    forwards*: TypedReduce_progress A mu H1.
    inverts wel.
    inverts* H2.
    +
    destruct(value_decidable (e_anno e A)); eauto.
    inverts wel.
    inverts* H0. inverts* H3.
    destruct x; eauto.
  -
    right. 
    inverts wel.
    forwards*: typing_regular Typ'.
    exists*.
  -
    right. 
    lets* [Val | [e' Red]]: IHTyp.
    +
    inverts Val. inverts Typ.
    inverts H6. 
    forwards: ptype_inf wel H4. auto.
    assert(wf_typ empty (t_all t_dyn)).
    pick fresh x and apply wf_typ_all; eauto.
    destruct(consist_decidable empty A0 (t_all t_dyn)); auto.
    inverts H7.
    *
    inverts H1; try solve[inverts H5;inverts* H9].
    forwards*: typing_regular H4. destructs~ H1.
    inverts H4. inverts H11.
    forwards*: pattern_type_all H0.
    *
    forwards*: typing_regular H4. destructs~ H7.
    inverts H0; inverts H3;
    try solve[exfalso; apply H9; eauto]. 
    inverts H11.
    exfalso; apply H9.   
    pick fresh x. 
    apply consist_all with (L :=union L
    (union L0
       (union (fv_te u)
          (union (fv_ee u)
             (union (fv_tt A) (union (fv_tt B) (fv_tt A1))))))); intros;eauto.
    exists. 
    eapply step_tappd; eauto.   
    +
    inverts Red.
    rewrite fill_tapp.  destruct e'; exists*.
  -
    right. 
    lets* [Val | [e' Red]]: IHTyp.
    + inverts* wel.
    +
    inverts* Red. 
    rewrite fill_ref.  destruct e'; exists*.
  -
    right. 
    lets* [Val | [e' Red]]: IHTyp.
    +
    inverts Val; inverts Typ.
    inverts H5.
    forwards*: ptype_inf H3.
    destruct(consist_decidable empty A0 (t_ref t_dyn)); eauto.
    inverts H5.
    *
    inverts* H0; try solve[inverts* H4;inverts* H7].
    forwards*: typing_regular H3. destructs~ H0.
    inverts H3. inverts H8.
    forwards*: pattern_type_ref H.
    inverts wel.
    exists. apply step_get; eauto.
    *
    inverts H; inverts H2;
    try solve[exfalso; apply H7; eauto].
    inverts wel.
    exists*.  
    +
    inverts Red. 
    rewrite fill_get. destruct e'; exists*.
  -
   right. 
   lets* [Val1 | [e1' Red1]]: IHTyp1.
   lets* [Val2 | [e2' Red2]]: IHTyp2.
   +
     inverts Typ1; inverts Val1.
     inverts H0.
    forwards*: ptype_inf H2.
    destruct(consist_decidable empty A0 (t_ref t_dyn)); eauto.
    inverts H5.
    *
    inverts* H3; try solve[inverts* H2;inverts* H7].
    forwards*: typing_regular H2. destructs~ H3.
    inverts H2. inverts H8.
    forwards*: pattern_type_ref H.
    lets wel': wel.
    inverts wel.
    inverts H9. rewrite H13 in *.
    forwards*: sto_ok_value H8.
    inverts Typ2.
    forwards*: consist_regular H16.
    destructs~ H18.
    forwards*: Typelist_progress wel' H20 H14 H17.
    inverts H21.
    inverts H0. 
    destruct x; eauto.
    exists.
    eapply step_set; eauto. 
    *
    inverts H; inverts H1;
    try solve[exfalso; apply H7; eauto].
    inverts wel.
    exists*.  
   +
     inverts Red2.
     rewrite fill_setr. 
    destruct e2'; exists*.
   +
     inverts Red1.
     forwards*: typing_regular Typ2.
    rewrite fill_setl. destruct e1'; exists*.
Qed.