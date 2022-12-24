Require Export Metalib.Metatheory.
Require Import LibTactics.

Require Import Definitions.
Require Import Infrastructure.
Require Import Lemmas.
Require Import Determinism.
Require Import Soundness.
Require Import Omega.




Lemma pvalue_expr: forall v,
 pvalue v -> expr v.
Proof.
  introv val.
  inductions val; eauto.
Qed.


Lemma value_expr: forall v,
 value v -> expr v.
Proof.
  introv val.
  inductions val; eauto.
  forwards*: pvalue_expr H.
Qed.


Lemma anno_inf: forall P p t t1 dir,
 typing nil P (e_anno p t) dir t1 ->
 exists t2, typing nil P p Inf t2.
Proof.
  introv typ.
  inverts* typ.
  inverts* H5.
  inverts* H0.
  inverts* H4. 
Qed.


Inductive tpre : typ -> typ -> Prop :=    
| tp_tvar : forall x,
    tpre (t_fvar x) (t_fvar x)
| tp_i : 
    tpre t_int t_int
| tp_all : forall L A B,
    (forall x, x \notin L ->
            tpre (A open_tt_var x) (B open_tt_var x)) ->
    tpre (t_all A) (t_all B)
| tp_dyn : forall (A:typ),
    type A ->
    tpre A t_dyn
| tp_abs : forall (A B C D:typ),
    tpre A C ->
    tpre B D ->
    tpre (t_arrow A B) (t_arrow C D)
| tp_unit : 
    tpre t_unit t_unit
| tp_ref : forall A B,
    tpre A B ->
    tpre (t_ref A) (t_ref B)
.




Inductive epre : exp -> exp -> Prop :=  
 | ep_var : forall (x:var),
    epre (e_fvar x) (e_fvar x)
 | ep_i i:
    epre (e_lit i) (e_lit i) 
 | ep_unit :
    epre e_unit e_unit 
 | ep_abs : forall (e1 e2:exp) (L:vars) A1 A2 B1 B2,
     ( forall x , x \notin  L  -> 
      epre  ( open_ee e1 (e_fvar x) )   ( open_ee e2 (e_fvar x) )  )  ->
      tpre A1 A2 ->
      tpre B1 B2 ->
     epre (e_abs A1 e1 B1) (e_abs A2 e2 B2)
 | ep_tabs : forall (e1 e2:exp) (L:vars) A1 A2,
      (forall x , x \notin  L  -> 
      epre  ( open_te e1 (t_fvar x) )   ( open_te e2 (t_fvar x) )  )  ->
      (forall X, X \notin L ->
      tpre (A1 open_tt_var X) (A2 open_tt_var X) ) ->
     epre (e_tabs e1 A1) (e_tabs e2 A2)
 | ep_app : forall (e1 e2 e1' e2':exp) ,
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_app e1 e2) (e_app e1' e2')
 | ep_tapp : forall (e1 e2:exp) A B,
     tpre A B ->
     epre e1 e2 ->
     epre (e_tapp e1 A) (e_tapp e2 B)
 | ep_anno : forall (e1 e2:exp) A B,
     tpre A B ->
     epre e1 e2 ->
     epre (e_anno e1 A) (e_anno e2 B)
 | ep_loc i:
     epre (e_loc i) (e_loc i) 
 | ep_ref : forall (e1 e2:exp),
     epre e1 e2 ->
     epre (e_ref e1) (e_ref e2)
 | ep_get : forall (e1 e2:exp),
     epre e1 e2 ->
     epre (e_get e1) (e_get e2)
 | ep_set : forall (e1 e2 e1' e2':exp) ,
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_set e1 e2) (e_set e1' e2')
.

Inductive mpre : sto -> sto -> Prop :=  
 | mp_nil : 
    mpre nil nil
 | mp_cons: forall v1 m1 v2 m2,
    epre v1 v2 ->
    mpre m1 m2 ->  
    mpre (v1::m1) (v2::m2). 


Inductive ppre : phi -> phi -> Prop :=  
 | pp_nil : 
    ppre nil nil
 | pp_cons: forall t1 m1 t2 m2,
    tpre t1 t2 ->
    ppre m1 m2 ->  
    ppre (t1::m1) (t2::m2). 


Inductive cpre : env -> env -> Prop :=
  | cp_nil: 
      cpre nil nil
  | cp_cons: forall E F x A1 A2,
      tpre A1 A2 ->
      cpre E F ->
      cpre ([(x ,bind_typ A1)] ++ E) ([(x, bind_typ A2)] ++ F)
  | cp_cons2: forall E F x,
      cpre E F ->
      cpre (x ~tvar ++ E) (x ~tvar ++ F)
.


Hint Constructors cpre tpre epre mpre ppre: core.


Lemma tpre_refl: forall A,
  type A -> 
  tpre A A.
Proof.
 introv type.
 inductions type; simpl; eauto.
Qed.



Hint Extern 1 (tpre ?A ?A) =>
 match goal with
 | H: type ?A |- _ => apply tpre_refl
 end : core.


Lemma epre_refl: forall e,
    expr e ->
    epre e e.
Proof.
  introv exp. inductions exp; simpl; eauto.
  pick fresh x. apply ep_tabs with (L:=union  L (union (fv_te e) (union (fv_ee e) (fv_tt A)))); intros;eauto.
  apply tpre_refl; auto.
Qed.


Lemma tpre_type: forall A1 A2,
    tpre A1 A2 ->
    type A1 /\ type A2.
Proof.
  introv ty. inductions ty; simpls~.
  -
  splits~.
  pick fresh x and apply type_all; eauto.
  forwards*: H0 x.
  pick fresh x and apply type_all; eauto.
  forwards*: H0 x.
  -
  destruct IHty1. destruct IHty2. splits~.
  -
  destruct IHty. splits~.
Qed.


Hint Resolve tpre_type : core.

Lemma tpre_wf_typ: forall E A B,
 tpre A B ->
 wf_typ E A ->
 wf_typ E B.
Proof.
  introv tp wft. gen E.
  inductions tp; intros; auto.
  - 
  inverts wft.
  pick fresh y and apply wf_typ_all.
  forwards: H3 y. eauto.
  forwards: H0 H1. eauto.
  simpl; eauto.
  - 
  inverts* wft.
  -
  inverts* wft.
Qed.


Lemma tpre_consist : forall E A1 B1 A2 B2,
  wf_env E ->
  consist E A1 B1 ->
  tpre A1 A2 ->
  tpre B1 B2 ->
  consist E A2 B2.
Proof.
  introv wfv s1 tp1 tp2. gen A2 B2.
  lets s1': s1.
  inductions s1; intros; 
  try solve[inverts tp2; inverts tp1].
  - inverts tp2; inverts tp1; eauto.
  - inverts tp2; inverts tp1; eauto.
  - inverts tp2; inverts tp1; eauto.
  - forwards*: tpre_wf_typ tp2.
    inverts* tp1.
  - forwards*: tpre_wf_typ tp1.
    inverts* tp2.
  - inverts tp1; inverts tp2; eauto.
    + 
    forwards*: consist_regular s1'. inverts H0. inverts H3.
    forwards*: tpre_wf_typ (t_arrow B1 B2) (t_arrow C D) H5.
    +
    forwards*: consist_regular s1'. inverts H0. inverts H4.
    forwards*: tpre_wf_typ (t_arrow A1 A2) (t_arrow C D) H0.
  - 
    lets tp1': tp1. lets tp2': tp2.
    inverts tp1; inverts tp2; eauto.
    +
    pick fresh y and apply consist_all.
    forwards*: H y. 
    +
    forwards*: consist_regular s1'.
    destruct H3. destruct H4.
    forwards*: tpre_wf_typ tp1'.
    +
    forwards*: consist_regular s1'.
    destruct H2. destruct H4.
    forwards*: tpre_wf_typ tp2'.
  -
    forwards*: tpre_wf_typ tp1.
    forwards*: tpre_wf_typ tp2.
    inverts* tp1; inverts* tp2. 
Qed.


Lemma epre_exp: forall e1 e2,
 epre e1 e2 ->
 expr e1 /\
 expr e2.
Proof.
  introv ep. 
  inductions ep; intros; try solve[
  forwards*: tpre_type H];
  try solve[inverts* IHep1];
  try solve[forwards*: IHep]; eauto.
  -
    split. 
    pick fresh y and apply expr_abs.
    forwards*: tpre_type H1.
    forwards*: tpre_type H2.
    forwards*: H0 y.
    pick fresh y and apply expr_abs.
    forwards*: tpre_type H1.
    forwards*: tpre_type H2.
    forwards*: H0 y.
  - split.
    pick fresh y and apply expr_tabs.
    forwards*: H0 y. 
    forwards*: H1 y. 
    forwards*: tpre_type H2. 
    pick fresh y and apply expr_tabs.
    forwards*: H0 y. 
    forwards*: H1 y. 
    forwards*: tpre_type H2.
Qed.


Lemma epre_expr: forall e1 e2,
 epre e1 e2 ->
 expr e1 ->
 expr e2.
Proof.
  introv ep lc. 
  inductions ep; intros; try solve[inverts~ lc; 
  forwards*: tpre_type H].
  -
  inverts lc.
  pick fresh x and apply expr_abs; eauto.
  forwards*: tpre_type H1.
  forwards*: tpre_type H2.
  -
  inverts lc.
  pick fresh x and apply expr_tabs; eauto.
  forwards*: H1 x.
  forwards*: tpre_type H2.
Qed.

Lemma epre_exprl: forall e1 e2,
 epre e1 e2 ->
 expr e2 ->
 expr e1.
Proof.
  introv ep lc.
  inductions ep; intros; try solve[inverts~ lc; 
  forwards*: tpre_type H].
  -
  inverts lc.
  pick fresh x and apply expr_abs; eauto.
  forwards*: tpre_type H1.
  forwards*: tpre_type H2.
  -
  inverts lc.
  pick fresh x and apply expr_tabs; eauto.
  forwards*: H1 x.
  forwards*: tpre_type H2.
Qed.


Lemma epre_pval: forall v1 v2,
 pvalue v1 ->
 epre v1 v2 ->
 pvalue v2.
Proof.
  introv val ep.
  inductions val; try solve[inverts* ep].
  -
  forwards*: epre_expr ep.
  inverts* ep.
  -
  forwards*: epre_expr ep.
  inverts* ep.
Qed.


Lemma epre_pvalr: forall v1 v2,
 pvalue v2 ->
 epre v1 v2 ->
 pvalue v1.
Proof.
  introv val ep.
  inductions val; try solve[inverts* ep].
  -
  forwards*: epre_exprl ep.
  inverts* ep.
  -
  forwards*: epre_exprl ep.
  inverts* ep.
Qed.
  


Lemma epre_val: forall v1 v2,
 value v1 ->
 epre v1 v2 ->
 value v2.
Proof.
  introv val ep.
  inductions val; try solve[inverts* ep].
  inverts ep.
  forwards*: epre_pval H5.
  forwards*: tpre_type H3. 
Qed.


Lemma epre_valr: forall v1 v2,
 value v2 ->
 epre v1 v2 ->
 value v1.
Proof.
  introv val ep.
  inductions val; try solve[inverts* ep].
  inverts ep.
  forwards*: epre_pvalr H5.
  forwards*: tpre_type H4. 
Qed.

  

Lemma epre_open: forall e1 e2 u1 u2 x,
 epre e1 e2 ->
 epre u1 u2 ->
 expr u1 ->
 expr u2 ->
 epre ([x ~> u1]e1) ([x ~> u2]e2).
Proof.
  introv ep1 ep2 lc1 lc2. gen u1 u2 x.
  inductions ep1; intros; 
  simpl; eauto.
  -  destruct (x == x0); eauto.
  - pick fresh x0.
      apply ep_abs with (L := union L
      (union (singleton x)(union (fv_te e1)(union (fv_te e2)
      (union (fv_te u1)(union (fv_te u2)(union (fv_ee e1)
      (union (fv_ee e2)(union (fv_ee u1)(union (fv_ee u2)
      (union (singleton x) (union (fv_tt A1)(union 
       (fv_tt A2) (union (fv_tt B1) (union (fv_tt B2) 
                                     (singleton x)))))))))))))))); intros; auto.
         forwards*: H0 x1 ep2 x. 
      rewrite subst_ee_open_ee_var; eauto. 
      rewrite subst_ee_open_ee_var; eauto.
  -
    apply ep_tabs with (L := union L
    (union (singleton x)
       (union (fv_te e1)
          (union (fv_te e2)
             (union (fv_te u1)
                (union (fv_te u2)
                   (union (fv_ee e1)
                      (union (fv_ee e2)
                         (union (fv_ee u1)
                            (union (fv_ee u2)
                               (union 
                                  (singleton x)
                                  (union 
                                   (fv_tt A1)
                                   (union 
                                   (fv_tt A2) 
                                   (singleton x)))))))))))))); intros;eauto.
    forwards*: H0 x0 ep2 x. 
    rewrite subst_ee_open_te_var; eauto. 
    rewrite subst_ee_open_te_var; eauto.
Qed.


Lemma  susbt_tt_type: forall A u1 x,
 type A ->
 type u1 ->
 type (subst_tt x u1 A).
Proof.
  introv typ1 typ2. gen x u1.
  inductions typ1; intros; unfold subst_tt; eauto.
  -
  destruct(X == x); eauto.
  -
  fold subst_tt.
  pick fresh y and apply type_all; eauto.
  rewrite subst_tt_open_tt_var; eauto. 
Qed.


Lemma tpre_open: forall t1 t2 u1 u2 x,
 tpre t1 t2 ->
 tpre u1 u2 ->
 type u1 ->
 type u2 ->
 tpre (subst_tt x u1 t1) (subst_tt x u2 t2).
Proof.
  introv ep1 ep2 lc1 lc2. gen u1 u2 x.
  inductions ep1; intros; 
  simpl; eauto.
  - destruct (x == x0); eauto.
  - pick fresh y.
    apply tp_all with (L := union L
    (union (singleton x)
       (union (singleton x)
          (union (fv_tt A)
             (union (fv_tt B)
                (union (fv_tt u1) (union (fv_tt u2) (singleton x))))))));intros;eauto.
    rewrite subst_tt_open_tt_var; eauto. 
    rewrite subst_tt_open_tt_var; eauto.
  - forwards*: susbt_tt_type H lc1.
Qed.



Lemma etpre_open: forall e1 e2 u1 u2 x,
 epre e1 e2 ->
 tpre u1 u2 ->
 type u1 ->
 type u2 ->
 epre (subst_te x u1 e1) (subst_te x u2 e2).
Proof.
  introv ep1 ep2 lc1 lc2. gen u1 u2 x.
  inductions ep1; intros; 
  simpl; eauto.
  - pick fresh y. 
    apply ep_abs with (L := union L
    (union (singleton x)
       (union (fv_te e1)
          (union (fv_te e2)
             (union (fv_ee e1)
                (union (fv_ee e2)
                   (union (singleton x)
                      (union (fv_tt A1)
                         (union (fv_tt A2)
                            (union (fv_tt B1)
                               (union (fv_tt B2)
                                  (union 
                                     (fv_tt u1)
                                     (union 
                                      (fv_tt u2) 
                                      (singleton x)))))))))))))); intros; auto.
    forwards*: H0 x0 ep2 x.
    rewrite subst_te_open_ee_var; eauto. 
    rewrite subst_te_open_ee_var; eauto.
    forwards*: tpre_open H1 ep2.
    forwards*: tpre_open H2 ep2.
  - pick fresh y. 
    apply ep_tabs with (L := union L
    (union (singleton x)
       (union (fv_te e1)
          (union (fv_te e2)
             (union (fv_ee e1)
                (union (fv_ee e2)
                   (union (singleton x)
                      (union (fv_tt A1)
                         (union (fv_tt A2)
                            (union (fv_tt u1)
                               (union 
                                  (fv_tt u2) 
                                  (singleton x))))))))))));intros; eauto.
    forwards*: H0 x0 ep2 x.
    rewrite subst_te_open_te_var; eauto. 
    rewrite subst_te_open_te_var; eauto.
    rewrite subst_tt_open_tt_var; eauto. 
    rewrite subst_tt_open_tt_var; eauto.
    forwards*: tpre_open H1 ep2.
  - apply ep_tapp.
    forwards*: tpre_open H lc1 lc2.
    forwards*: IHep1 ep2 x.
  - apply ep_anno.
    forwards*: tpre_open H lc1 lc2.
    forwards*: IHep1 ep2 x.
Qed.



Lemma env_less_precise_binds : forall x A E F,
    binds x (bind_typ A) E ->
    cpre E F ->
    exists B, binds x (bind_typ B) F /\ tpre A B.
Proof.
  introv bind cp.
  inductions cp; try solve[inverts* bind];eauto.
  inverts* bind. inverts* H0.
  forwards*: IHcp.
  inverts* H1.
  inverts* bind. inverts* H.
  forwards*: IHcp.
  inverts* H0.
Qed.



Lemma cpre_notin: forall x E F,
  x `notin` dom E ->
 cpre E F ->
 x \notin dom F.
Proof.
  introv uq cp.
  inductions cp; try solve[inverts* uq]; eauto.
Qed.


Lemma cpre_uniq: forall E F,
 uniq E ->
 cpre E F ->
 uniq F.
Proof.
  introv uq cp.
  inductions cp; try solve[inverts* uq]; eauto.
  inverts* uq.
  forwards*: IHcp.
  forwards*: cpre_notin cp.
  inverts* uq.
  forwards*: IHcp.
  forwards*: cpre_notin cp.
Qed.


Lemma binds_tpre: forall x T T' E1 E2,
 uniq E1 ->
 uniq E2 ->
 cpre E1 E2 ->
 binds x (bind_typ T) E1 ->
 binds x (bind_typ T') E2 ->
 tpre T T'.
Proof.
  introv uq1 uq2 cp bind1 bind2. gen x T T'.
  inductions cp; intros;try solve[inverts uq1;inverts uq2;inverts bind1;inverts* bind2].
  inverts uq1;inverts uq2;inverts bind1;inverts* bind2;
  try solve[inverts* H0;inverts* H1]; try solve[inverts* H0];
  try solve[inverts* H1].
  inverts* H0. 
  exfalso. apply H6;eauto.
  inverts H1.
  exfalso. apply H4;eauto.
  inverts bind1;inverts* bind2;try solve[inverts* H;inverts* H0];
  try solve[inverts* H0].
  forwards*: IHcp x0 T T'.
  inverts* uq1.
  inverts* uq2.
Qed.

(* 
Lemma binds_tpre_sub: forall x T T' E1 E2,
 uniq E1 ->
 uniq E2 ->
 cpre E1 E2 ->
 binds x (bind_sub T) E1 ->
 binds x (bind_sub T') E2 ->
 tpre T T'.
Proof.
  introv uq1 uq2 cp bind1 bind2. gen x T T'.
  inductions cp; intros;try solve[inverts uq1;inverts uq2;inverts bind1;inverts* bind2].
  inverts uq1;inverts uq2;inverts bind1;inverts* bind2;
  try solve[inverts* H0;inverts* H1]; try solve[inverts* H0];
  try solve[inverts* H1].
  inverts bind1;inverts* bind2;try solve[inverts* H0;inverts* H1];
  try solve[inverts* H1].
  simpl_env in *.
  inverts* H0. inverts* uq2.
  exfalso. apply H5;eauto.
  inverts* H1. inverts* uq1.
  exfalso. apply H5;eauto.
  forwards*: IHcp x0 T T'.
  inverts* uq1.
  inverts* uq2.
Qed. *)


Lemma mpre_length:forall mu1 mu2,
 mpre mu1 mu2 ->
 length mu1 = length mu2.
Proof.
  introv mp.
  inductions mp; simpl; eauto.
Qed.


Lemma mpre_app:forall mu1 mu2 mu3 mu4,
 mpre mu1 mu2 ->
 mpre mu3 mu4 ->
 mpre (mu1++mu3) (mu2++mu4).
Proof.
  introv mp1 mp2.
  inductions mp1; simpl; eauto.
Qed.


Lemma store_lookup_epre: forall l mu1 mu2,
 mpre mu1 mu2 ->
 epre (store_lookup l mu1) (store_lookup l mu2).
Proof.
  introv mp.
  inductions l;
  try solve[inductions mp; eauto].
Qed.

Lemma epre_principle_type: forall e1 e2,
 epre e1 e2 ->
 tpre (principle_type e1) (principle_type e2).
Proof.
  introv ep.
  inductions ep; eauto.
Qed.



Lemma ptype_tpre : forall l mu1 mu2 A,
 mpre mu1 mu2 ->
 ptype mu1 (e_loc l) A ->
 exists B, ptype mu2 (e_loc l) B /\ tpre A B.
Proof.
  introv mp ptyp. gen mu1 mu2 A.
  inductions l; intros.
  inverts ptyp.
  forwards*: store_lookup_epre 0 mp.
  forwards*: epre_principle_type H.
  inverts ptyp.
  forwards*: store_lookup_epre (S l) mp.
  forwards*: epre_principle_type H.
Qed.


Lemma epre_tpre : forall mu1 mu2 p1 p2 A B,
 pvalue p1 ->
 mpre mu1 mu2 ->
 epre p1 p2 ->
 ptype mu1 p1 A ->
 ptype mu2 p2 B ->
 tpre A B.
Proof.
  introv pval mp ep ptyp1 ptyp2.
  inductions pval; try solve[
  inverts* ep; inverts ptyp1; inverts* ptyp2].
  inverts* ep; inverts ptyp1; inverts* ptyp2.
  forwards*: store_lookup_epre l mp.
  forwards*: epre_principle_type H.
Qed.



Lemma dmatch_tpre_abs2: forall t1 t2 t3 t5 ,
 tpre t1 t2 ->
 pattern_abs t1 t3  ->
 pattern_abs t2 t5 ->
 tpre t3 t5 .
Proof.
  introv tp dm1 dm2. gen t3 t5 .
  inductions tp; intros; eauto;
  try solve[inverts* dm1];
  try solve[inverts* dm2];
  try solve[inverts* dm2; inverts* dm1;inverts* H].
Qed.


Lemma dmatch_tpre_ref2: forall t1 t2 t3 t5 ,
 tpre t1 t2 ->
 pattern_ref t1 t3  ->
 pattern_ref t2 t5 ->
 tpre t3 t5 .
Proof.
  introv tp dm1 dm2. gen t3 t5 .
  inductions tp; intros; eauto;
  try solve[inverts* dm1];
  try solve[inverts* dm2];
  try solve[inverts* dm2; inverts* dm1;inverts* H].
Qed.


Lemma dmatch_tpre_all2: forall t1 t2 t3 t5 ,
 tpre t1 t2 ->
 pattern_all t1 t3  ->
 pattern_all t2 t5 ->
 tpre t3 t5 .
Proof.
  introv tp dm1 dm2. gen t3 t5.
  inductions tp; intros; 
  try solve[inverts dm1];
  try solve[inverts dm1;inverts* dm2];
  try solve[inverts dm2].
  inverts dm2. inverts dm1. inverts H.
  pick fresh x.
  forwards*: H1 x.
  pick fresh x and apply tp_all; eauto.
Qed.


Theorem precise_type: forall E1 E2 e e' T T' P mu,
   P |== mu ->
   cpre E1 E2 -> 
   epre e e' ->  
   typing E1 P e Inf T ->
   typing E2 P e' Inf T'->
   tpre T T'.
Proof.
    introv well cp ep Typ1 Typ2.
    gen T T'.
    inductions ep; intros;
    try solve[inverts* Typ1; inverts* Typ2].
    - 
      inverts Typ1. inverts Typ2.
      forwards*: binds_tpre H3 H5.
    -
      inverts* Typ1.
      inverts* Typ2.
      forwards*: IHep1 H4 H7.
      forwards*: dmatch_tpre_abs2 H1 H2.
      inverts* H0.
    -
      inverts* Typ1.
      inverts* Typ2.
      forwards*: IHep H6 H9.
      forwards*: dmatch_tpre_all2 H0 H5.
      inverts* H1.
      pick fresh y.
      forwards*: H10 y.
      assert(open_tt B1 B = subst_tt y B (B1 open_tt_var y)).
      rewrite ( subst_tt_intro y); eauto.
      rewrite ( subst_tt_intro y); eauto.
      rewrite H4.
      forwards*: tpre_open H1 H.
    -
      inverts* Typ1.
      inverts* Typ2.
      forwards*: type_from_wf_typ H4.
    - inverts* Typ1.
      inverts* Typ2.
      forwards*: IHep H3 H5.
      forwards*: dmatch_tpre_ref2 H0 H1.
      inverts* H2.
Qed.


Lemma env_less_precise_binds2 : forall x E F,
    binds x bind_tvar E ->
    cpre E F ->
    binds x bind_tvar F.
Proof.
  introv bind cp.
  inductions cp; try solve[inverts* bind];eauto.
  inverts* bind. inverts* H0.
  inverts* bind. inverts* H.
Qed.


Lemma tpre_wf_typ2: forall E F A B,
 tpre A B ->
 cpre E F ->
 wf_typ E A ->
 wf_typ F B.
Proof.
  introv tp wft. gen E F.
  inductions tp; intros; 
  try solve[inverts* H];auto.
  -
    inverts H.
    forwards*: env_less_precise_binds2 H2.
  - 
  inverts H1.
  pick fresh y and apply wf_typ_all.
  assert(cpre ((y, bind_tvar) :: E) ((y, bind_tvar) :: F)); eauto.
  eapply cp_cons2; eauto.
Qed.

Lemma cpre_wf_env: forall E1 E2,
 cpre E1 E2 ->
 wf_env E1 ->
 wf_env E2.
Proof.
  introv cp wf.
  inductions cp; eauto.
  inverts wf.
  forwards*: tpre_wf_typ2 H cp.
  forwards*: IHcp.
  forwards*: cpre_notin H5.
  inverts wf.
  forwards*: IHcp.
  forwards*: cpre_notin cp.
Qed.



Lemma cpre_consist : forall E F A1 B1,
  wf_env E ->
  cpre E F ->
  consist E A1 B1 ->
  consist F A1 B1.
Proof.
  introv wfv cp con. gen F.
  inductions con; intros; 
  try solve[forwards: cpre_wf_env cp;auto ].
  -
    forwards*: cpre_wf_env cp.
    forwards*: tpre_wf_typ2 H0.
  -
    assert(tpre A A). 
    forwards*: type_from_wf_typ H0.
    forwards*: tpre_wf_typ2 H1 H0.
    forwards*: cpre_wf_env cp.
  -
    assert(tpre A A). 
    forwards*: type_from_wf_typ H0.
    forwards*: tpre_wf_typ2 H1 H0.
    forwards*: cpre_wf_env cp.
  -
    pick fresh x and apply consist_all; auto.
Qed.



Lemma tpre_sim : forall E F A1 B1 A2 B2,
  wf_env E ->
  cpre E F ->
  consist E A1 B1 ->
  tpre A1 A2 ->
  tpre B1 B2 ->
  consist F A2 B2.
Proof.
  introv wfv cp s1 tp1 tp2.
  forwards*: tpre_consist s1 tp1 tp2.
  forwards*:  cpre_consist cp H.
Qed.


Lemma dmatch_tpre_abs: forall t1 t2 t4,
 tpre t1 t4 ->
 pattern_abs t1 t2 ->
 exists t5, pattern_abs t4 t5 /\
 tpre t2 t5.
Proof.
  introv tp dm. gen t2.
  inductions tp; intros; eauto;
  try solve[inverts* dm].
  inverts* dm.
  exists(t_arrow t_dyn t_dyn). splits*.
  inverts* H.
Qed.



Lemma dmatch_tpre_ref: forall t1 t2 t4,
 tpre t1 t4 ->
 pattern_ref t1 t2 ->
 exists t5, pattern_ref t4 t5 /\
 tpre t2 t5.
Proof.
  introv tp dm. gen t2.
  inductions tp; intros; eauto;
  try solve[inverts* dm].
  inverts* dm.
  exists(t_ref t_dyn). splits*.
  inverts* H.
Qed.

Lemma dmatch_tpre_all: forall t1 t2 t4,
 tpre t1 t4 ->
 pattern_all t1 t2 ->
 exists t5, pattern_all t4 t5 /\
 tpre t2 t5.
Proof.
  introv tp dm. gen t2.
  inductions tp; intros; eauto;
  try solve[inverts* dm].
  inverts dm. 
  inverts H.
  exists(t_all t_dyn). splits.
  eauto. pick fresh x and apply tp_all; eauto.
  inverts H.
  exists(t_all t_dyn). splits.
  eauto. pick fresh x and apply tp_all; eauto.
Qed.


Theorem tpre_chk: forall E1 E2 e1 e2 T T' P mu,
   P |== mu ->
   cpre E1 E2 -> 
   epre e1 e2 ->  
   typing E1 P e1 Chk T ->
   tpre T T' ->
   typing E2 P e2 Chk T'.
Proof.
  introv well cp ep typ tp. gen E1 E2 T T' P mu.
  inductions ep; intros;
  try solve[forwards*: cpre_wf_env cp].
  - inverts typ.
    inverts H0.
    forwards*: env_less_precise_binds H5. inverts H0. inverts H1.
    forwards*: cpre_uniq cp.
    forwards*: tpre_sim H H3 tp.
    forwards*: cpre_wf_env cp.
  -
    forwards*: cpre_wf_env cp.
    inverts typ. inverts H1.
    assert(tpre t_int t_int);eauto.
    forwards*: tpre_sim H0 H1 tp.
  -
    forwards*: cpre_wf_env cp.
    inverts typ. inverts H1.
    assert(tpre t_unit t_unit);eauto.
    forwards*: tpre_sim H0 H1 tp.
  -
    inverts typ. inverts H4.
    forwards*: consist_regular H3.
    destructs~ H4.
    assert(tpre (t_arrow A1 B1) (t_arrow A2 B2)). eauto.
    forwards*: tpre_sim cp H3 H7 tp.
    eapply typ_consist; eauto.
    pick fresh y and apply  typ_abs; eauto.
  -
    inverts typ. inverts H3.
    forwards*: consist_regular H2.
    destructs~ H3.
    assert(tpre (t_all A1) (t_all A2)). eauto.
    forwards*: tpre_sim cp H2 H6 tp.
    eapply typ_consist; eauto.
    pick fresh y.
    eapply  typ_tabs with (L := union L
    (union L0
       (union (fv_te e1)
          (union (fv_te e2)
             (union (fv_ee e1)
                (union (fv_ee e2)
                   (union (fv_tt A1)
                      (union (fv_tt A2)
                         (union (fv_tt T)
                            (union (fv_tt T')
                               (union (dom E1)
                                  (union 
                                     (dom E2)
                                     (union 
                                      (fv_tt_env E1)
                                      (fv_tt_env E2))))))))))))) ); intros.
    forwards*: H7 y.
  -
    inverts typ. inverts H0.
    forwards*: typing_chk H6.
    forwards: typing_regular H6.
    assert(tpre A1 A1).
    destructs~ H1.
    forwards: type_from_wf_typ H4. auto.
    forwards*: IHep1 H2 H0.
    inverts H4.
    forwards*: precise_type ep1 H6 H8.
    forwards*: dmatch_tpre_abs H4 H3.
    lets(tt1&mma&tpp1): H9.
    inverts tpp1; try solve[inverts mma].
    forwards*: IHep2 H12 H7.
    forwards*: tpre_sim H H14 tp.
  -
    inverts typ. inverts H1.
    forwards: typing_chk H8. 
    forwards: typing_regular H8.
    assert(tpre A2 A2).
    destructs~ H2.
    forwards: type_from_wf_typ H5. auto.
    forwards: IHep cp H3 H1 well.
    inverts H5.
    forwards: precise_type well ep H8 H9; auto.
    forwards*: dmatch_tpre_all H5 H7.
    lets(tt1&mma&tpp1): H10.
    inverts tpp1; try solve[inverts mma].
    assert(tpre (open_tt B0 A) (open_tt B1 B)).
    forwards*: tpre_type H.
    pick fresh y.
    forwards: H12 y. auto.
    rewrite (subst_tt_intro y); eauto.
    assert((open_tt B1 B) =
      (subst_tt y B (B1 open_tt_var y))).
    rewrite (subst_tt_intro y); eauto.
    rewrite H14.
    forwards*: tpre_open H12 H.
    forwards*: tpre_sim H0 H11 tp.
    eapply typ_consist with (A:= (open_tt B1 B)); eauto.
    eapply typ_tapp;eauto.
    forwards*: tpre_wf_typ2 cp H4.
  -
    inverts typ. inverts H1.
    forwards*: IHep H.
    forwards*: tpre_sim H0 H tp.
  -
    inverts typ. inverts H0.
    forwards*: consist_regular H.
    destructs~ H0.
    forwards*: type_from_wf_typ H1.
    assert(tpre  (t_ref (store_Tlookup i P))  (t_ref (store_Tlookup i P))).
    eauto.
    forwards*: tpre_sim H H7 tp.
    eapply typ_consist; eauto.
    forwards*: consist_regular H8.
    destructs~ H9.
    apply typ_loc; eauto.
    inverts* H10.
  -
    inverts typ. inverts H0.
    forwards: typing_chk H4. 
    forwards: typing_regular H4.
    assert(tpre A0 A0).
    destructs~ H1.
    forwards: type_from_wf_typ H3. auto.
    forwards: IHep cp H2 H0 well.
    inverts H3.
    forwards: precise_type well ep H4 H6; auto.
    assert(tpre (t_ref A0) (t_ref A)); auto.
    forwards*: tpre_sim cp H H7 tp.
  -
    inverts typ. inverts H0.
    forwards: typing_chk H5. 
    forwards: typing_regular H5.
    assert(tpre A0 A0).
    destructs~ H1.
    forwards: type_from_wf_typ H4. auto.
    forwards: IHep cp H3 H0 well.
    inverts H4.
    forwards: precise_type well ep H5 H7; auto.
    forwards*: dmatch_tpre_ref H4 H2.
    lets(tt1&mma&tpp1): H8.
    inverts tpp1; try solve[inverts mma].
    forwards*: tpre_sim cp H tp.
  -
    inverts typ. inverts H0.
    forwards: typing_chk H6. 
    forwards: typing_regular H6.
    assert(tpre A0 A0).
    destructs~ H1.
    forwards: type_from_wf_typ H4. auto.
    forwards: IHep1 cp H2 H0 well.
    inverts H4.
    forwards: precise_type well ep1 H6 H8; auto.
    forwards*: dmatch_tpre_ref H4 H3.
    lets(tt1&mma&tpp1): H9.
    inverts tpp1; try solve[inverts mma].
    assert(tpre t_unit t_unit). auto.
    forwards*: tpre_sim cp H H10 tp.
Qed.

Theorem SGG_chk: forall E1 E2 e1 e2 T P mu,
   P |== mu ->
   cpre E1 E2 -> 
   epre e1 e2 ->  
   typing E1 P e1 Chk T ->
   exists T', typing E2 P e2 Chk T' /\  tpre T T'.
Proof.
  introv well cp ep typ.
  assert(tpre T T).
  apply tpre_refl; eauto.
  forwards*: tpre_chk typ H.
Qed.


Theorem SGG_both: forall E1 E2 e1 e2 dir T P mu,
   P |== mu ->
   cpre E1 E2 -> 
   epre e1 e2 ->  
   typing E1 P e1 dir T ->
   exists T', typing E2 P e2 dir T' /\  tpre T T'.
Proof.
  introv wel cp ep Typ1.
  destruct dir.
  -
  forwards*: typing_chk Typ1. 
  forwards*: SGG_chk ep H.
  inverts H0. inverts H1.
  inverts H0.
  forwards*: precise_type Typ1 H3.
  -
  forwards*: SGG_chk Typ1.
Qed.



Lemma tdynamic_guarantee: forall P1 P2 mu1 mu2 e1 e2 e1' A B A1 B1,
 P1 |== mu1 ->
 P2 |== mu2 ->  
 mpre mu1 mu2 ->
 epre e1 e2 ->  
 tpre A B ->
 value e1 ->
 typing nil P1 e1 Inf A1 ->
 typing nil P2 e2 Inf B1 -> 
 TypedReduce (e1,mu1) A ((r_e e1'),mu1) ->
 exists e2' , TypedReduce (e2,mu2) B ((r_e e2'),mu2) 
 /\ epre e1' e2'.
Proof.
  introv wel1 wel2 mp ep tp val typ1 typ2 red. gen P1 P2 e2 mu2 B.
  inductions red; intros; eauto.
  - 
    inverts* ep. inverts typ2. 
    + forwards*: anno_inf typ1. inverts H2. 
      forwards*: ptype_inf H3.
      inverts wel1.
      forwards*: ptype_uniq H0 H2. subst. 
      forwards*: epre_pval H6.
      inverts H7.
      forwards*: ptype_inf H9.
      forwards*: epre_tpre H2 H7.
      forwards*: tpre_consist H1 H12 tp.
Qed.




Lemma Typlists_epre2: forall P1 P2 mu1 mu2 v1 v2 v1' A B A1 B1 A2 B2,
 P1 |== mu1 ->
 P2 |== mu2 ->  
 mpre mu1 mu2 ->
 typing nil P1 v1 Chk A ->
 typing nil P2 v2 Chk B ->
 value v1 ->
 epre v1 v2 ->
 tpre A1 B1 ->
 tpre A2 B2 ->
 TypeLists (v1,mu1) (A2 :: A1 :: nil) ((r_e v1'),mu1) ->
 exists v2', TypeLists (v2,mu2) (B2 :: B1 :: nil) ((r_e v2'),mu2) /\ 
 epre v1' v2'.
Proof.
  introv wel1 wel2 mp typ1 typ2 val ep tp1 tp2 tlist.
  inverts tlist. inverts H5. inverts H7.
  forwards*: tpre_type tp1. forwards*: tpre_type tp2.
  forwards*: TypedReduce_prv_value H2.
  forwards*: TypedReduce_preservation H2.
  assert(typing empty P1 v' Chk t_dyn); eauto.
  forwards*: TypedReduce_prv_value H3.
  forwards*: TypedReduce_preservation H3.
  assert(typing empty P1 v1' Chk A1); eauto.
  forwards*: TypedReduce_prv_value H3.
  forwards*: TypedReduce_preservation H3.
  inverts typ1. inverts typ2.
  forwards*: tdynamic_guarantee ep tp2 H2. inverts H15. inverts H16.
  forwards*: epre_val ep.
  forwards*: TypedReduce_preservation H15.
  forwards*:tdynamic_guarantee tp1 H3. inverts H19. inverts H20.
  forwards*: epre_val H21.
Qed.



Lemma replace_epre:forall mu1 mu2 l v1 v2,
 mpre mu1 mu2 ->
 epre v1 v2 ->
 mpre (replace l v1 mu1) (replace l v2 mu2).
Proof.
  introv mp ep. gen mu1 mu2 v1 v2.
  inductions l; intros;
  try solve[inductions mp;  simpl; eauto].
Qed.


Lemma dynamic_guarantee_dir: forall e1 e2 P1 P2 mu1 mu1' mu2 e1' dir T1 T2, 
 P1 |== mu1 ->
 P2 |== mu2 ->  
 mpre mu1 mu2 ->
 epre e1 e2 -> 
 typing nil P1 e1 dir T1 ->
 typing nil P2 e2 dir T2 -> 
 step ( e1, mu1) ((r_e e1'),mu1') ->
 exists e2' mu2', step (e2,mu2) ((r_e e2'),mu2') /\ 
 epre e1' e2' /\ mpre mu1' mu2'.
Proof.
  introv wel1 wel2 mp ep typ1 typ2 red. gen e1' P1 P2 mu1 mu2 dir T1 T2.
  inductions ep; intros;
  try solve[inverts* red; try solve[
    destruct F; unfold fill in H;inverts* H
  ];try solve[inverts* H0]].
  - inverts* red; try solve[
    destruct F; unfold fill in H;inverts* H
    ];
    try solve[inverts H4].
  - inverts* red; try solve[
    destruct F; unfold fill in H;inverts* H
    ].
    inverts* H5.
    inverts wel2.
    exists*.
  - inverts* red; try solve[
    destruct F; unfold fill in H;inverts* H
    ].
    inverts* H5.
    inverts wel2.
    exists*.
  - inverts* red; try solve[
    destruct F; unfold fill in H3;inverts* H3
    ].
    inverts* H9.
    inverts wel2.
    forwards*: epre_expr (e_abs A1 e1 B1) (e_abs A2 e2 B2). 
    exists*.
  -
    inverts* red; try solve[
    destruct F; unfold fill in H2;inverts* H2
    ].
    inverts* H8.
    inverts wel2.
    forwards*: epre_expr (e_tabs e1 A1) (e_tabs e2 A2). 
    exists*.
  - inverts* red; try solve[inverts H4].
    + 
    inverts typ1. 
    * 
    inverts typ2. 
    destruct F; unfold fill in *; inverts* H. 
    -- 
    forwards*: IHep1 H4. inverts H. inverts H0.
    exists (e_app x e2') x0. split. inverts H2.
    forwards: epre_expr ep2; auto.
    rewrite fill_appl. rewrite fill_appl.
    forwards*: epre_expr ep2.
    split*.   
    -- 
    forwards*: IHep2 H4. inverts H. inverts H0.
    exists (e_app e1' x) x0. split*. inverts H2.
    forwards: epre_val ep1; auto.
    rewrite fill_appr. rewrite fill_appr.
    inverts* H.
    *
    inverts typ2. inverts H1. inverts H5. 
    destruct F; unfold fill in *; inverts* H. 
    -- 
    forwards*: IHep1 H4. inverts H. inverts H1.
    exists (e_app x e2') x0. split*. inverts H2.
    forwards: epre_expr ep2; auto.
    rewrite fill_appl. rewrite fill_appl.
    forwards*: epre_expr ep2.   
    -- 
    forwards*: IHep2 H4. inverts H. inverts H1.
    exists (e_app e1' x) x0. split*. inverts H2.
    forwards: epre_val ep1; auto.
    rewrite fill_appr. rewrite fill_appr.
    inverts* H.
    +
    inverts ep1. inverts H3.
    forwards*: tpre_type H1. 
    forwards*: pattern_type_abs H7. inverts H0.
    inverts typ1. 
    * 
    inverts typ2. inverts H16. inverts H18.
    forwards*: dmatch_tpre_abs2 H7 H14. inverts H0.
    forwards*: Typlists_epre2 ep2 H11 H21 H8.
    inverts H0. inverts H2.
    forwards*: epre_val ep2. 
    assert(epre (e_abs A1 e B1) (e_abs A3 e3 B3)); eauto.
    forwards*: epre_expr H18.
    inverts wel2.
    exists*. split*. split*.
    apply ep_anno; eauto. apply ep_anno; eauto.
    forwards*: epre_exp H15. inverts H26.
    pick fresh xx.
    assert((e3 ^^ x) = [xx ~> x] (e3 ^ xx)).
    rewrite ( subst_ee_intro xx); eauto.
    rewrite (subst_ee_intro xx); eauto.
    rewrite H26.
    forwards*: H9 xx.
    forwards*: epre_open H29 H15.
    *
    inverts typ2. inverts H14. inverts H20. 
    forwards*: dmatch_tpre_abs2 H7 H17. inverts H14.
    inverts H2.
    forwards*: Typlists_epre2 ep2 H11 H20 H8.
    inverts H2. inverts H14.
    forwards*: epre_val ep2. 
    assert(epre (e_abs A1 e B1) (e_abs A3 e3 B3)); eauto.
    forwards*: epre_expr H19.
    inverts wel2.
    exists*. split*. split*.
    apply ep_anno; eauto. apply ep_anno; eauto.
    forwards*: epre_exp H15. inverts H28.
    pick fresh xx.
    assert((e3 ^^ x) = [xx ~> x] (e3 ^ xx)).
    rewrite ( subst_ee_intro xx); eauto.
    rewrite (subst_ee_intro xx); eauto.
    rewrite H28.
    forwards*: H9 xx.
    forwards*: epre_open H31 H15.
  - 
    inverts* red;try solve[
    destruct F; unfold fill in H0;inverts* H0
    ]; try solve[inverts* H5].
    + 
    inverts typ1;
    destruct F; unfold fill in H0;inverts* H0.
    *
    inverts typ2. 
    forwards*: IHep H5. inverts H0. 
    inverts H1. inverts H0. inverts H6.
    exists* (e_tapp x B) x0. split*. 
    forwards*: epre_expr ep.
    rewrite fill_tapp. rewrite fill_tapp.
    forwards*: tpre_type H.
    simpl. split*.   
    *
    inverts typ2. 
    inverts H4. inverts H2.
    forwards*: IHep H5. inverts H2. inverts H4.
    inverts H2. inverts H6.
    exists (e_tapp x B) x0. split. 
    forwards: epre_expr ep; auto.
    rewrite fill_tapp. rewrite fill_tapp.
    forwards*: tpre_type H.
    simpl; split*.   
    +
    forwards*: typing_regular typ1. destructs~ H0.
    inverts H1. inverts H7.
    forwards*: tpre_type H. inverts H1.
    forwards*: epre_expr ep.
    inverts* ep. inverts H14. 
    forwards*: dmatch_tpre_all H12 H6.
    lets(tt1&mma&tpp1): H10.
    inverts tpp1; try solve[inverts mma].
    inverts H1.
    forwards*: pattern_type_all mma.
    exists. split.
    eapply step_tap;eauto.
    split*.
    apply ep_anno.
    pick fresh xx.
    assert(open_tt B3 B = subst_tt xx B (B3 open_tt_var xx)).
    rewrite ( subst_tt_intro xx); eauto.
    rewrite ( subst_tt_intro xx); eauto.
    rewrite H11.
    forwards*: H14 xx.
    forwards*: tpre_open H15 H.
    apply ep_anno.
    pick fresh xx.
    forwards*: H16 xx.
    assert(open_tt A2 B = subst_tt xx B (A2 open_tt_var xx)).
    rewrite ( subst_tt_intro xx); eauto.
    rewrite ( subst_tt_intro xx); eauto.
    rewrite H15.
    forwards*: H16 xx.
    forwards*: tpre_open H19 H.
    pick fresh xx.
    assert(open_te e2 B = subst_te xx B (e2 open_te_var xx)).
    rewrite ( subst_te_intro xx); eauto.
    rewrite ( subst_te_intro xx); eauto.
    rewrite H11.
    forwards*: H13 xx.
    forwards*: etpre_open H15 H.
  - inverts* red; try solve[
    destruct F; unfold fill in H0;inverts* H0
    ]; try solve[inverts* H5].
    +
    forwards*: typing_regular typ2.
    inverts H0. 
    forwards*: value_decidable H3.
    forwards*: anno_inf typ1. inverts H4.
    forwards*: anno_inf typ2. inverts H4.
    forwards*: IHep H6. inverts H4. inverts H8.
    inverts* H0.
    assert(epre (e_anno e1 A) (e_anno e2 B));eauto.
    forwards*: epre_valr H0.
    inverts* H4.
    exists* (e_anno x1 B) x2. 
    +
    forwards*: anno_inf typ1. inverts H0.
    forwards*: anno_inf typ2. inverts H0.
    forwards*: tdynamic_guarantee H H7.
    inverts* H0. inverts* H3.
    forwards*: epre_val ep.
    inverts wel2.
    exists* x1 mu2. 
  - inverts* red; try solve[
    destruct F; unfold fill in H;inverts* H
    ].
    inverts* wel2.
    forwards*:ptype_tpre H5.
    inverts H1. inverts* H2.
    exists* (e_anno (e_loc i) x) mu2.
  - inverts* red; try solve[
    destruct F; unfold fill in H;inverts* H
    ]; try solve[inverts* H4].
    +
    inverts typ1. 
    * 
    inverts typ2. inverts H1. inverts H5. 
    destruct F; unfold fill in *; inverts* H. 
    --
    forwards*: IHep H4. inverts H. inverts H1.
    exists (e_ref x) x0. split*. 
    rewrite fill_ref.
    inverts* H.
    assert((e_ref x) = fill refCtx x).
    eauto.
    rewrite H;eauto.
    *
    inverts typ2. 
    destruct F; unfold fill in *; inverts* H. 
    --
    forwards*: IHep H4. inverts H. inverts H0.
    exists (e_ref x) x0. split*. 
    rewrite fill_ref.
    inverts* H.
    assert((e_ref x) = fill refCtx x).
    eauto.
    rewrite H;eauto.
    +
    forwards*: mpre_length mp.
    rewrite H.
    forwards*: epre_val ep.
    inverts wel2.
    exists (e_loc (length mu2)) (mu2++e2::nil).
    split*. split*.
    apply mpre_app; eauto.
  -
    inverts* red; try solve[
    destruct F; unfold fill in H;inverts* H
    ]; try solve[inverts* H4].
    +
    inverts typ1. 
    * 
    inverts typ2. inverts H1. inverts H5. 
    destruct F; unfold fill in *; inverts* H. 
    --
    forwards*: IHep H4. inverts H. inverts H1.
    exists (e_get x) x0. split*. 
    rewrite fill_get.
    inverts* H.
    assert((e_get x) = fill getCtx x).
    eauto.
    rewrite H;eauto.
    *
    inverts typ2. 
    destruct F; unfold fill in *; inverts* H. 
    --
    forwards*: IHep H4. inverts H. inverts H0.
    exists (e_get x) x0. split*. 
    rewrite fill_get.
    inverts* H.
    assert((e_get x) = fill getCtx x).
    eauto.
    rewrite H;eauto.
    +
    inverts ep. inverts H5. 
    inverts typ2. 
    *
    inverts H0. inverts H8.
    forwards*: store_lookup_epre l0 mp.
    inverts wel2.
    forwards*: dmatch_tpre_ref2 H4 H5. inverts H8.
    exists* (e_anno (store_lookup l0 mu2) A0) mu2.
    *
    inverts H6. inverts H7.
    forwards*: store_lookup_epre l0 mp.
    inverts wel2.
    forwards*: dmatch_tpre_ref2 H4 H0. inverts H8.
    exists* (e_anno (store_lookup l0 mu2) T2) mu2.
  -
    inverts* red; try solve[
    destruct F; unfold fill in H;inverts* H
    ]; try solve[inverts* H4].
    + 
    inverts typ1. 
    * 
    inverts typ2. inverts H1. inverts H5. 
    destruct F; unfold fill in *; inverts* H. 
    -- 
    forwards*: IHep1 H4. inverts H. inverts H1.
    exists (e_set x e2') x0. split. inverts H2.
    forwards: epre_expr ep2; auto.
    rewrite fill_setl. rewrite fill_setl.
    forwards*: epre_expr ep2.
    split*.   
    -- 
    forwards*: IHep2 H4. inverts H. inverts H1.
    exists (e_set e1' x) x0. split*. inverts H2.
    forwards: epre_val ep1; auto.
    rewrite fill_setr. rewrite fill_setr.
    inverts* H.
    *
    inverts typ2. 
    destruct F; unfold fill in *; inverts* H. 
    -- 
    forwards*: IHep1 H4. inverts H. inverts H0.
    exists (e_set x e2') x0. split*. inverts H2.
    forwards: epre_expr ep2; auto.
    rewrite fill_setl. rewrite fill_setl.
    forwards*: epre_expr ep2.   
    -- 
    forwards*: IHep2 H4. inverts H. inverts H0.
    exists (e_set e1' x) x0. split*. inverts H2.
    forwards: epre_val ep1; auto.
    rewrite fill_setr. rewrite fill_setr.
    inverts* H.
    +
    inverts typ2. 
    *
    inverts H0.
    forwards*: store_lookup_epre l0 mp.
    forwards*: epre_principle_type H0.
    inverts ep1. inverts H13.
    inverts H10. inverts H13.
    inverts typ1. inverts H12. inverts H18.
    forwards*: dmatch_tpre_ref2 H8 H3. inverts H12.
    forwards*: Typlists_epre2 ep2 H1 H17 H7. 
    inverts H12. inverts* H13. 
    forwards*: epre_val ep2.
    forwards*: replace_epre l0 mp H14.
    inverts wel2.
    exists e_unit (replace l0 x mu2).
    split*. 
    *
    inverts typ1. inverts H10.
    forwards*: store_lookup_epre l0 mp.
    forwards*: epre_principle_type H.
    inverts ep1. inverts H15.
    inverts H6. inverts H15.
    forwards*: dmatch_tpre_ref2 H8 H1.
    inverts H10.
    forwards*: Typlists_epre2 H0 H16 H7. 
    inverts H10. inverts* H14. 
    forwards*: epre_val ep2.
    forwards*: replace_epre l0 mp H15.
    inverts wel2.
    exists e_unit (replace l0 x mu2).
    split*. 
Qed.















