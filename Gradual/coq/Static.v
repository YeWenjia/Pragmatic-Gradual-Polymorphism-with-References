
Require Import LibTactics.

Require Import Definitions.
Require Import Infrastructure.
Require Import Lemmas.
Require Import Determinism.
Require Import Soundness.
Require Import Lia.


(** * STATIC *)


Inductive dexp : Set :=
  | de_bvar   : nat -> dexp
  | de_fvar   : var -> dexp
  | de_lit    : nat -> dexp
  | de_unit   : dexp
  | de_anno   : dexp -> typ -> dexp
  | de_app    : dexp -> dexp -> dexp
  | de_abs    : typ -> dexp  -> dexp 
  | de_tabs   : dexp -> dexp 
  | de_tapp   : dexp -> typ -> dexp
  | de_loc    : nat -> dexp
  | de_ref    : dexp -> dexp
  | de_get    : dexp -> dexp
  | de_set    : dexp -> dexp -> dexp
.


Fixpoint dopen_te_rec (k : nat) (f : typ) (e : dexp) {struct e} : dexp :=
  match e with
  | de_bvar i       => de_bvar i
  | de_fvar x       => de_fvar x
  | de_lit i        => de_lit i
  | de_unit        => de_unit
  | de_loc x      => de_loc x
  | de_app e1 e2    => de_app (dopen_te_rec k f e1) (dopen_te_rec k f e2)
  | de_abs A e1   => de_abs (open_tt_rec k f A) (dopen_te_rec k f e1) 
  | de_anno e1 A    => de_anno (dopen_te_rec k f e1) (open_tt_rec k f A) 
  | de_tabs e1     => de_tabs (dopen_te_rec (S k) f e1) 
  | de_tapp e1 A     => de_tapp (dopen_te_rec k f e1) (open_tt_rec k f A) 
  | de_ref e1     => de_ref (dopen_te_rec k f e1) 
  | de_get e1     => de_get (dopen_te_rec k f e1)
  | de_set e1 e2     => de_set (dopen_te_rec k f e1) (dopen_te_rec k f e2)
  end.

Fixpoint dopen_ee_rec (k : nat) (f : dexp) (e : dexp) {struct e} : dexp :=
  match e with
  | de_bvar i       => if k == i then f else (de_bvar i)
  | de_fvar x       => de_fvar x
  | de_loc x      => de_loc x
  | de_lit i        => de_lit i
  | de_unit        => de_unit
  | de_app e1 e2    => de_app (dopen_ee_rec k f e1) (dopen_ee_rec k f e2)
  | de_abs A e1   => de_abs A (dopen_ee_rec (S k) f e1)
  | de_anno e1 A    => de_anno (dopen_ee_rec k f e1) A 
  | de_tabs e1     => de_tabs (dopen_ee_rec k f e1) 
  | de_tapp e1 A     => de_tapp (dopen_ee_rec k f e1) A 
  | de_ref e1     => de_ref (dopen_ee_rec k f e1) 
  | de_get e1     => de_get (dopen_ee_rec k f e1)
  | de_set e1 e2     => de_set (dopen_ee_rec k f e1) (dopen_ee_rec k f e2)
  end.


Definition dopen_te e T := dopen_te_rec 0 T e.
Definition dopen_ee e1 e2 := dopen_ee_rec 0 e2 e1.


  Notation "t 'dopen_ee_var' x" := (dopen_ee t (de_fvar x)) (at level 67).

  Notation "t 'dopen_te_var' a" := (dopen_te t (t_fvar a)) (at level 67).





Inductive dtyp_static : typ -> Prop :=
  | dtyp_static_nat:
      dtyp_static t_int
  | dtyp_static_fvar: forall i,
      dtyp_static (t_fvar i)
  | dtyp_static_arrow: forall A B,
      dtyp_static A ->
      dtyp_static B ->
      dtyp_static (t_arrow A B)
  | dtyp_static_all: forall L A,
      (forall x, x \notin L -> dtyp_static (A open_tt_var x)) ->
      dtyp_static (t_all A)
  | dtyp_ref: forall A,
      dtyp_static A ->
      dtyp_static (t_ref A) 
   | dtyp_static_unit:
      dtyp_static t_unit
.

Inductive dterm_static : exp -> Prop :=
  | dterm_static_var: forall x,
      dterm_static (e_fvar x)
  | dterm_static_nat : forall i,
      dterm_static (e_lit i)
  | dterm_static_unit : 
      dterm_static e_unit
  | dterm_static_tabs : forall L V e1,
      (forall x, x \notin L -> dterm_static (e1 open_te_var x)) ->
      (forall X, X \notin L -> dtyp_static (V open_tt_var X)) ->
      dterm_static (e_tabs e1 V)
  | dterm_static_abs : forall L e1 A B,
     dtyp_static A ->
     dtyp_static B ->
      (forall x, x \notin L -> dterm_static (e1 open_ee_var x)) ->
      dterm_static (e_abs A e1 B)
  | dterm_static_app : forall e1 e2,
      dterm_static e1 ->
      dterm_static e2 ->
      dterm_static (e_app e1 e2)
  | dterm_static_tapp : forall e A,
      dterm_static e ->
      dtyp_static A ->
      dterm_static (e_tapp e A)
  | dterm_static_ref : forall e,
      dterm_static e ->
      dterm_static (e_ref e)
  | dterm_static_get : forall e,
      dterm_static e ->
      dterm_static (e_get e)
  | dterm_static_set : forall e1 e2,
      dterm_static e1 ->
      dterm_static e2 ->
      dterm_static (e_set e1 e2)
  | dterm_static_loc : forall i,
      dterm_static (e_loc i)
  | dterm_static_anno : forall e A,
      dterm_static e ->
      dtyp_static A ->
      dterm_static (e_anno e A)
.

Inductive denv_static : env -> Prop :=
  | denv_static_empty : denv_static empty
  | denv_static_typ : forall E x T,
      denv_static E ->
      dtyp_static T ->
      wf_typ E T ->
      x \notin dom E ->
      denv_static ( x ~: T ++ E)
  | denv_static_tvar : forall E x,
      denv_static E ->
      x \notin dom E ->
      denv_static (x ~tvar ++ E)
.


Inductive phi_static : phi -> Prop :=
  | phi_static_typ : forall E,
      (forall l,  l < length (E) -> 
      dtyp_static (store_Tlookup l E)) ->
      phi_static (E).



Inductive eq: env -> typ -> typ -> Prop :=  
  | eq_int : forall E,
      wf_env E ->
      eq E t_int t_int
  | eq_unit : forall E,
      wf_env E ->
      eq E t_unit t_unit
  | eq_var : forall E x,
      wf_env E ->
      wf_typ E (t_fvar x) ->
      eq E (t_fvar x) (t_fvar x)
  | eq_fun : forall E A1 A2 B1 B2,
      eq E B1 A1 ->
      eq E A2 B2 ->
      eq E (t_arrow A1 A2) (t_arrow B1 B2)
  | eq_all: forall L E A B ,
      (forall x, x \notin L ->
      eq (x ~tvar ++ E) (A open_tt_var x) (B open_tt_var x)) ->
      eq E (t_all A) (t_all B)
  | eq_ref : forall E A B,
      eq E A B ->
      eq E (t_ref A) (t_ref B)
.

Inductive styping : env -> phi -> exp -> dirflag -> typ -> Prop :=
  | styp_var : forall E P x T,
      wf_env E ->
      binds x (bind_typ T) E ->
      styping E P (e_fvar x) Inf T
  | styp_nat : forall E P i,
      wf_env E ->
      styping E P (e_lit i) Inf (t_int)
  | styp_unit : forall E P,
      wf_env E ->
      styping E P e_unit Inf t_unit
  | styp_loc : forall E P l,
       wf_env E ->
      l < length P ->
      wf_typ E (store_Tlookup l P) ->
      styping E P (e_loc l) Inf (t_ref (store_Tlookup l P))
  | styp_app : forall E P e1 e2 A B,
      styping E P e1 Inf (t_arrow A B) ->
      styping E P e2 Chk A ->
      styping E P (e_app e1 e2) Inf B
  | styp_abs : forall L E P A B e,
      (forall x, x \notin L ->
            styping (x ~: A ++ E) P (e open_ee_var x) Chk B) ->
      styping E P (e_abs A e B) Inf (t_arrow A B)
  | styp_anno : forall E P e A,
     styping E P e Chk A ->
     styping E P (e_anno e A) Inf A
  | styp_tabs : forall E P e A L,
      ( forall a , a \notin  L  -> 
      styping  ( a ~tvar ++ E) P ( e open_te_var a )  Chk  ( A open_tt_var a )  )  ->
     styping E P (e_tabs e A) Inf (t_all A)
  | styp_tapp : forall E P e A B,
      wf_typ E A ->
     styping E P e Inf (t_all B) ->
     styping E P (e_tapp e A) Inf  (open_tt B A )
  | styp_eq : forall E P e B A,
     eq E A B ->
     styping E P e Inf A ->
     styping E P e Chk B
  | styp_ref : forall E P e A,
     styping E P e Inf A ->
     styping E P (e_ref e) Inf (t_ref A)
  | styp_get : forall E P e A1,
     styping E P e Inf (t_ref A1) ->
     styping E P (e_get e) Inf A1
  | styp_set : forall E P e1 e2 A1,
     styping E P e1 Inf (t_ref A1) ->
     styping E P e2 Chk A1->
     styping E P (e_set e1 e2) Inf t_unit
.


Inductive sstyping : env -> phi -> exp -> dirflag -> typ -> dexp -> Prop :=
  | sstyp_var : forall E P x T,
      wf_env E ->
      binds x (bind_typ T) E ->
      sstyping E P (e_fvar x) Inf T (de_fvar x)
  | sstyp_nat : forall E P i,
      wf_env E ->
      sstyping E P (e_lit i) Inf (t_int) (de_lit i)
  | sstyp_unit : forall E P,
      wf_env E ->
      sstyping E P e_unit Inf t_unit de_unit
  | sstyp_loc : forall E P l,
       wf_env E ->
      l < length P ->
      wf_typ E (store_Tlookup l P) ->
      sstyping E P (e_loc l) Inf (t_ref (store_Tlookup l P)) (de_loc l)
  | sstyp_app : forall E P e1 e2 A B t1 t2,
      sstyping E P e1 Inf (t_arrow A B) t1 ->
      sstyping E P e2 Chk A t2 ->
      sstyping E P (e_app e1 e2) Inf B (de_app t1 t2)
  | sstyp_abs : forall L E P A B e t,
      (forall x, x \notin L ->
            sstyping (x ~: A ++ E) P (e open_ee_var x) Chk B (t dopen_ee_var x)) ->
      sstyping E P (e_abs A e B) Inf (t_arrow A B) (de_abs A t)
  | sstyp_anno : forall E P e A t,
     sstyping E P e Chk A t ->
     sstyping E P (e_anno e A) Inf A (de_anno t A)
  | sstyp_tabs : forall E P e A L t,
      ( forall a , a \notin  L  -> 
      sstyping  ( a ~tvar ++ E) P ( e open_te_var a )  Chk  ( A open_tt_var a )   ( t dopen_te_var a ))  ->
     sstyping E P (e_tabs e A) Inf (t_all A) (de_tabs t)
  | sstyp_tapp : forall E P e A B t,
      wf_typ E A ->
     sstyping E P e Inf (t_all B) t ->
     sstyping E P (e_tapp e A) Inf  (open_tt B A ) (de_tapp t A)
  | sstyp_eq : forall E P e B A t,
     eq E A B ->
     sstyping E P e Inf A t ->
     sstyping E P e Chk B t
  | sstyp_ref : forall E P e A t,
     sstyping E P e Inf A t ->
     sstyping E P (e_ref e) Inf (t_ref A) (de_ref t)
  | sstyp_get : forall E P e A1 t,
     sstyping E P e Inf (t_ref A1) t ->
     sstyping E P (e_get e) Inf A1 (de_get t)
  | sstyp_set : forall E P e1 e2 A1 t1 t2,
     sstyping E P e1 Inf (t_ref A1) t1 ->
     sstyping E P e2 Chk A1 t2 ->
     sstyping E P (e_set e1 e2) Inf t_unit (de_set t1 t2)
.


Inductive atyping : env -> phi -> dexp -> dirflag -> typ -> Prop :=
| atyp_var : forall E P x T,
    wf_env E ->
    binds x (bind_typ T) E ->
    atyping E P (de_fvar x) Inf T
| atyp_nat : forall E P i,
    wf_env E ->
    atyping E P (de_lit i)  Inf (t_int)
| atyp_unit : forall E P,
    wf_env E ->
    atyping E P de_unit  Inf t_unit
| atyp_loc : forall E P l,
    wf_env E ->
    l < length P ->
    wf_typ E (store_Tlookup l P) ->
    atyping E P (de_loc l)  Inf  (t_ref (store_Tlookup l P))
| atyp_app : forall E P e1 e2 A B,
    atyping E P e1 Inf (t_arrow A B) ->
    atyping E P e2 Chk  A ->
    atyping E P (de_app e1 e2)  Inf  B
| atyp_abs : forall L E P A B e,
    (forall x, x \notin L ->
            atyping (x ~: A ++ E) P (e dopen_ee_var x) Chk  B) ->
    atyping E P (de_abs A e)  Inf  (t_arrow A B)
| atyp_anno : forall E P e A,
    atyping E P e Chk A ->
    atyping E P (de_anno e A)  Inf  A
| atyp_tabs : forall E P e A L,
    ( forall a , a \notin  L  -> 
    atyping  ( a ~tvar ++ E) P ( e dopen_te_var a )  Chk  ( A open_tt_var a )  )  ->
    atyping E P (de_tabs e) Inf (t_all A)
| atyp_tapp : forall E P e A B,
    wf_typ E A ->
    atyping E P e  Inf  (t_all B) ->
    atyping E P (de_tapp e A)  Inf  (open_tt B A )
| atyp_ref : forall E P e A,
    atyping E P e Inf  A ->
    atyping E P (de_ref e) Inf (t_ref A)
| atyp_get : forall E P e A1,
    atyping E P e  Inf (t_ref A1) ->
    atyping E P (de_get e) Inf A1
| atyp_set : forall E P e1 e2 A1,
    atyping E P e1  Inf (t_ref A1) ->
    atyping E P e2 Chk A1->
    atyping E P (de_set e1 e2) Inf t_unit
| atyp_eq : forall E P e A B,
    atyping E P e Inf A ->
    eq E A B ->
    atyping E P e Chk B
.





Inductive aatyping : env -> phi -> dexp -> dirflag -> typ -> exp -> Prop :=
| aatyp_var : forall E P x T,
    wf_env E ->
    binds x (bind_typ T) E ->
    aatyping E P (de_fvar x) Inf T (e_fvar x)
| aatyp_nat : forall E P i,
    wf_env E ->
    aatyping E P (de_lit i)  Inf (t_int) (e_lit i)
| aatyp_unit : forall E P,
    wf_env E ->
    aatyping E P de_unit  Inf  t_unit e_unit
| aatyp_loc : forall E P l,
    wf_env E ->
    l < length P ->
    wf_typ E (store_Tlookup l P) ->
    aatyping E P (de_loc l) Inf (t_ref (store_Tlookup l P)) (e_loc l)
| aatyp_app : forall E P e1 e2 A B t1 t2,
    aatyping E P e1 Inf (t_arrow A B) t1 ->
    aatyping E P e2  Chk A t2 ->
    aatyping E P (de_app e1 e2) Inf B (e_app t1 t2)
| aatyp_abs : forall L E P A B e t,
    (forall x, x \notin L ->
            aatyping (x ~: A ++ E) P (e dopen_ee_var x)  Chk B (t open_ee_var x) ) ->
    aatyping E P (de_abs A e) Inf (t_arrow A B) (e_abs A t B)
| aatyp_anno : forall E P e A t,
    aatyping E P e  Chk A t ->
    aatyping E P (de_anno e A) Inf A (e_anno t A)
| aatyp_tabs : forall E P e A L t,
    ( forall a , a \notin  L  -> 
    aatyping  ( a ~tvar ++ E) P ( e dopen_te_var a )   Chk ( A open_tt_var a ) ( t open_te_var a ) )  ->
    aatyping E P (de_tabs e) Inf (t_all A) (e_tabs t A)
| aatyp_tapp : forall E P e A B t,
    wf_typ E A ->
    aatyping E P e Inf (t_all B) t ->
    aatyping E P (de_tapp e A)  Inf (open_tt B A ) (e_tapp t A) 
| aatyp_ref : forall E P e A t,
    aatyping E P e Inf A t ->
    aatyping E P (de_ref e) Inf (t_ref A) (e_ref t)
| aatyp_get : forall E P e A1 t,
    aatyping E P e Inf (t_ref A1) t ->
    aatyping E P (de_get e) Inf A1 (e_get t)
| aatyp_set : forall E P e1 e2 A1 t1 t2,
    aatyping E P e1 Inf (t_ref A1) t1 ->
    aatyping E P e2 Chk A1 t2 ->
    aatyping E P (de_set e1 e2) Inf t_unit (e_set t1 t2)
| aatyp_eq : forall E P e A t B,
    aatyping E P e Inf A t ->
    eq E A B ->
    aatyping E P e Chk B t
.




Inductive dstep : conf -> conf -> Prop :=    (* defn step *)
 | dstep_eval : forall mu mu' F e1 e2,
     wellformed F ->
     dstep (e1, mu) ((e2), mu') ->
     dstep ((fill F e1), mu) (( (fill F e2)), mu')
  | dstep_beta : forall (A1:typ) (e:exp) (B1 A2 B2:typ) u t mu,
     sto_ok mu ->
     pvalue u ->
     expr (e_abs A1 e B1) ->
     dstep ((e_app  ( (e_anno  ( (e_abs A1 e B1) )  (t_arrow A2 B2)) )  (e_anno u t)), mu) (((e_anno (e_anno  (open_ee  e (e_anno u A1) )  B1) B2)), mu)
 | dstep_u : forall (u:exp) (A:typ) mu,
     sto_ok mu ->
     pvalue u ->
     ptype mu u A ->
     dstep (u, mu) (( (e_anno u A)), mu)
 | dstep_anno : forall (e:exp) (A:typ) (e':exp) mu mu',
     not(value (e_anno e A)) ->
     dstep (e, mu) (( e'), mu') ->
     dstep ((e_anno e A), mu) (((e_anno e' A)), mu')
 | dstep_annov : forall (A:typ) B u mu,
     sto_ok mu ->
     pvalue u ->
     dstep ((e_anno (e_anno u B) A), mu) ((e_anno u A), mu)
 | dstep_tap : forall (e:exp) (A B C:typ) mu,
     expr (e_anno  (e_tabs e A) (t_all B)) ->
     dstep ((e_tapp (e_anno  (e_tabs e A) (t_all B)) C),mu) (((e_anno (e_anno (open_te e C ) (open_tt  A C )) (open_tt  B C ))),mu)
 | dstep_set : forall l A B u t mu,
     sto_ok mu ->
     pvalue u ->
     principle_type (store_lookup l mu) = B ->
     dstep ((e_set (e_anno (e_loc l)  (t_ref A)) (e_anno u t)), mu) ((e_unit), (replace l (e_anno u B) mu))
 | dstep_new : forall (v:exp) mu,
     sto_ok mu ->
     value v ->
     dstep ((e_ref v), mu) (( (e_loc (length mu))), (mu ++ v::nil))
 | dstep_get : forall (A:typ) l mu,
     sto_ok mu ->
     dstep ((e_get (e_anno (e_loc l) (t_ref A))), mu) (((e_anno (store_lookup l mu) A)), mu)
.

(** Properties for static *)


Hint Constructors aatyping atyping sstyping denv_static dterm_static dtyp_static styping eq dstep: core.


Lemma eq_type: forall A B x n,
 x `notin` (fv_tt A) ->
 x `notin` (fv_tt B) ->
 open_tt_rec n x A = open_tt_rec n x B ->
 A = B.
Proof.
  introv nt1 nt2 eq. gen B n x.
  inductions A; intros;try solve[].
  -
  inductions B; simpl in *; inverts* eq0;
  unfold open_tt in *; inverts* H0.
  destruct(n0 == n); try solve[inverts* e];
  try solve[inverts* H1].
  -
  inductions B; simpl in *; inverts* eq0;
  unfold open_tt in *; inverts* H0.
  +
  forwards* h1: IHA1 H2.
  forwards* h2: IHA2 H1.
  inverts h1. inverts* h2.
  +
  destruct(n0 == n); try solve[inverts* e];
  try solve[inverts* H1].
  -
  inductions B; simpl in *; inverts* eq0;
  unfold open_tt in *; inverts* H0;
  destruct(n0 == n); try solve[inverts* e];
  try solve[inverts* H1].
  -
  inductions B; simpl in *; inverts* eq0;
  unfold open_tt in *; inverts* H0;
  destruct(n0 == n); try solve[inverts* e];
  try solve[inverts* H1].
  destruct(n1 == n); try solve[inverts* e];
  try solve[inverts* H1].
  destruct(n1 == n0); try solve[inverts* e];
  try solve[inverts* H1].
  destruct(n1 == n0); try solve[inverts* e];
  try solve[inverts* H1].
  inverts* H1. inverts* e.
  exfalso. apply nt2. eauto.
  -
  inductions B; simpl in *; inverts* eq0;
  unfold open_tt in *; inverts* H0.
  destruct(n0 == n); try solve[inverts* e];
  try solve[inverts* H1].
  inverts* H1. inverts* e.
  exfalso. apply nt1. eauto.
  -
  inductions B; simpl in *; inverts* eq0;
  unfold open_tt in *; inverts* H0.
  destruct(n0 == n); try solve[inverts* e];
  try solve[inverts* H1].
  forwards*: IHA H1.
  inverts* H.
  -
  inductions B; simpl in *; inverts* eq0;
  unfold open_tt in *; inverts* H0.
  destruct(n0 == n); try solve[inverts* e];
  try solve[inverts* H1].
  forwards*: IHA H1.
  inverts* H.
  -
  inductions B; simpl in *; inverts* eq0;
  unfold open_tt in *; inverts* H0.
  destruct(n0 == n); try solve[inverts* e];
  try solve[inverts* H1].
Qed.


Lemma eq_left: forall A B E,
 eq E A B ->
 A = B.
Proof.
  introv eq.
  inductions eq; eauto.
  - inverts* IHeq1.  inverts* IHeq2.
  - pick fresh x.
    forwards* h1: H0 x.
    forwards*: eq_type h1.
    inverts* H1.
  - inverts* IHeq. 
Qed.



Lemma eq_rel: forall E A,
dtyp_static A ->
 wf_typ E A ->
 wf_env E ->
 eq E A A.
Proof.
  introv sta ty ev.
  inductions ty; eauto; try solve[inverts sta].
  -
  inverts* sta.
  -
  inverts sta.
  pick fresh x.
  apply eq_all with (L := union L
  (union L0
     (union (fv_tt A)
        (union (dom E) (fv_tt_env E)))));intros.
  forwards: H2 x0; auto.
  -
  inverts* sta.
Qed.


Lemma eq_right: forall A B E,
dtyp_static A ->
 wf_env E ->
 wf_typ E A ->
 wf_typ E B ->
 A = B ->
 eq E A B.
Proof.
  introv sta ev wf1 wf2 eq.
  inverts* eq.
  apply eq_rel; auto.
Qed.

Lemma sstyping_atyping: forall e1 e2 G P dir A,
  sstyping G P e1 dir A e2 ->
  atyping G P e2 dir A.
Proof.
  introv typ.
  inductions typ; eauto.  
Qed.



Lemma aatyping_styping: forall dir e1 e2 G P A,
 aatyping G P e1 dir A e2 ->
 styping G P e2 dir A.
Proof.
  introv typ.
  inductions typ; eauto.
Qed.



Lemma dtyp_static_eq: forall E A B,
    dtyp_static A ->
    dtyp_static B ->
    consist E A B ->
    eq E A B.
Proof.
  introv ta tb con.
  inductions con; eauto; try solve[inverts ta];
  try solve[inverts tb];
  try solve[inverts ta;inverts tb].
  -
  inverts ta; inverts* tb.
  -
  inversions tb. inverts ta.
  pick fresh y and apply eq_all.
  forwards ~ : H3 y.
  -
  inverts ta. inverts* tb.
Qed. 



Lemma eq_consist: forall E A B,
    eq E A B ->
    consist E A B.
Proof.
  introv con.
  inductions con; eauto.
Qed. 


Lemma dtyp_static_dtype : forall A,
    dtyp_static A ->
    type A.
Proof.
  introv ty. inductions ty; simpls~.
  pick fresh x and apply type_all;eauto.
Qed.


Hint Resolve dtyp_static_dtype : core.

Lemma dterm_static_dterm: forall e,
    dterm_static e ->
    expr e.
Proof.
  introv dm. inductions dm; eauto.
Qed.


Lemma styping_typing : forall E P e dir A,
  styping E P e dir A ->
  typing E P e dir A.
Proof.
    introv typ.
    inductions typ;eauto.
    forwards*: eq_consist H.
Qed.



Lemma dmatch_static_ref : forall A A1,
    pattern_ref A A1 ->
    dtyp_static A ->
    dtyp_static A1 .
Proof.
  introv mat st. inductions mat; simpls~.
Qed.


Lemma dmatch_static_abs : forall A A1,
    pattern_abs A A1 ->
    dtyp_static A ->
    dtyp_static A1 .
Proof.
  introv mat st. inductions mat; simpls~.
Qed.

Lemma dmatch_static_all : forall A A1,
    pattern_all A A1 ->
    dtyp_static A ->
    dtyp_static A1 .
Proof.
  introv mat st. inductions mat; simpls~.
  inverts st.
Qed.


Lemma denv_static_dtyp: forall e x T,
    denv_static e ->
    binds x (bind_typ T) e ->
    dtyp_static T.
Proof.
  introv dm bd. inductions dm; try solve[inverts bd].
  -
  analyze_binds bd.
  inverts* BindsTacVal.
  -
  analyze_binds bd.
Qed.




Lemma static_open: forall e1 u1  x,
 dtyp_static e1 ->
 dtyp_static u1 ->
 type u1 ->
 dtyp_static (subst_tt x u1 e1).
Proof.
  introv ts1 ts2 typ1. gen u1 x.
  inductions ts1; intros; 
  simpl; eauto.
  -
  destruct (i == x); eauto.
  -
  pick fresh y and apply dtyp_static_all.
  rewrite subst_tt_open_tt_var; eauto. 
Qed.




Definition Dtyping_static_preserve dir T := 
  match dir with 
  | Inf => dtyp_static T
  | Chk  => True
  end.




Lemma dtyping_static_preserve : forall E e P dir T,
    typing E P e dir T ->
    denv_static E ->
    dterm_static e ->
    phi_static P ->
    Dtyping_static_preserve dir T.
Proof.
  introv Hty Hen Htm Hpi.
  inductions Hty; auto; unfold Dtyping_static_preserve in *;simpl; auto.
  -
  forwards*: denv_static_dtyp H0.
  -
  inverts Hpi.
  forwards*: H2 l.
  -
  inverts Htm.
  forwards* h1: IHHty1 H2.
  forwards* h3: dmatch_static_abs H. inverts* h3.
  -
  inverts* Htm.
  -
  inverts* Htm.
  -
  inverts* Htm.
  -
  inverts* Htm.
  forwards* h1: IHHty.
  inverts H0; try solve[inverts h1].
  inverts h1.
    pick fresh y.
    rewrite (subst_tt_intro y); eauto.
    forwards*: H1 y.
    forwards*: static_open H0 H4.
  -
  inverts* Htm.
  -
  inverts* Htm.
  forwards* h1: IHHty.
  forwards* h2: dmatch_static_ref h1.
  inverts* h2.
Qed.





Lemma typing_styping : forall E P e dir A,
  dterm_static e ->
  denv_static E ->
  phi_static P ->
  dtyp_static A ->
  typing E P e dir A ->
   styping E P e dir A.
Proof.
  introv es vs ps ts typ.
  lets typ': typ.
  inductions typ;eauto; try solve[inverts es].
  -
    inverts es.
    forwards* h1: dtyping_static_preserve typ1.
    forwards* h2: dmatch_static_abs H.
    inverts* h2.
    forwards*: IHtyp1.
    forwards* h3: dtyping_static_preserve typ2.
    inverts* H; try solve[inverts h1].
  -
    inverts es.
    forwards h1: typing_regular typ'.
    destructs~ h1. inverts H3.
    pick fresh x and apply styp_abs.
    forwards*: H0.
  -
    inverts* es.
  -
    inverts es.
    pick fresh x. 
    apply styp_tabs with (L := union L
    (union L0
       (union (fv_te e)
          (union (fv_ee e)
             (union (fv_tt A) (union (dom E) (fv_tt_env E)))))));intros.
    forwards*: H0.
  -
    inverts es.
    forwards* h1: dtyping_static_preserve typ.
    forwards* h2: dmatch_static_all H0.
    inverts* h2.
    forwards*: IHtyp.
    inverts* H0; try solve[inverts h1].
  -
    forwards* h1: dtyping_static_preserve typ.
    forwards*: dtyp_static_eq H.
  -
    inverts* es.
    inverts* ts.
  -
    inverts es.
    forwards* h1: dtyping_static_preserve typ.
    forwards* h2: dmatch_static_ref H.
    inverts* h2.
    forwards*: IHtyp.
    inverts* H; try solve[inverts h1].
  -
    inverts es.
    forwards* h1: dtyping_static_preserve typ1.
    forwards* h2: dmatch_static_ref H.
    inverts* h2.
    forwards*: IHtyp1.
    forwards* h3: dtyping_static_preserve typ2.
    inverts* H; try solve[inverts h1].
Qed.



Lemma  eq_sym: forall E t1 t2,
 eq E t1 t2 ->
 eq E t2 t1.
Proof.
  introv eq.
  inductions eq;intros; try solve[inductions eq0;eauto];eauto.
Qed.


Lemma  eq_static: forall E t1 t2,
 eq E t1 t2 ->
 dtyp_static t1 ->
 dtyp_static t2 .
Proof.
  introv eq sta. gen E t2.
  inductions sta;intros; try solve[inductions eq0;eauto];eauto.
  -
  inverts eq0.
  forwards*:  eq_sym H2.
  -
  inverts eq0.
  pick fresh x and apply dtyp_static_all;eauto.
Qed.


Lemma eq_refl: forall t e,
 wf_env e ->
 wf_typ e t ->
 dtyp_static t ->
 eq e t t.
Proof.
  introv we ev dt. gen e.
  inductions dt;intros;auto; try solve[inverts ev].
  -
    inverts* ev.
  -
  inverts ev.
  pick fresh y and apply eq_all;eauto.
  -
  inverts* ev.
Qed.




Lemma styping_chk: forall E e P A,
denv_static E ->
phi_static P ->
 dterm_static e ->
 styping E P e Inf A ->
 styping E P e Chk A.
Proof.
  introv es ps se typ.
  eapply styp_eq; eauto.
  forwards h2: styping_typing typ.
    forwards h1: dtyping_static_preserve h2; auto.
    unfold Dtyping_static_preserve in *.
    forwards*: eq_refl h1.
Qed.



Lemma fill_chk_chk: forall G e E P B,
 denv_static G ->
 phi_static P ->
 dterm_static e ->
 styping G P (fill E e) Chk B ->
 dtyp_static B ->
 exists A, styping G P e Chk A.
Proof.
  introv es ps te typ st.
  destruct E; unfold fill in *; inverts* typ;
  try solve[inverts* H0].
  - inverts H0.
    forwards h2: styping_typing H5.
    forwards h1: dtyping_static_preserve h2; auto.
    unfold Dtyping_static_preserve in *.
    inverts h1.
    forwards*: styping_chk H5.
  -
    inverts H0.
    forwards*: styping_chk H6.
  -
    inverts H0.
    forwards*: styping_chk H4.
  -
    inverts H0.
    forwards*: styping_chk H5.
Qed.


Lemma fill_static: forall F e,
  dterm_static (fill F e) ->
  dterm_static e.
Proof.
 introv dt.
  destruct F; unfold fill in *; auto;
  try solve[inverts dt; auto].
Qed.


Lemma eq_trans_size: forall E A B C n,
 size_typ A + size_typ B + size_typ C < n ->
 eq E A B ->
 eq E B C ->
 eq E A C.
Proof.
  introv sz eq1 eq2. gen E A B C.
  induction n;intros; 
  try solve[lia].
  inductions eq1;eauto.
  -
  inductions eq2;simpl in *;auto.
  forwards: IHn eq2_1 eq1_1. lia.
  forwards: IHn eq1_2 eq2_2. lia.
  auto.
  -
  inductions eq2;simpl in *;auto.
  pick fresh x and apply eq_all.
  forwards h1: H x; auto.
  forwards h2: H1 x; auto.
  forwards: IHn h1 h2.
  rewrite size_open_tt.
  rewrite size_open_tt.
  rewrite size_open_tt.
  lia.
  auto.
  -
  inductions eq2;simpl in *;auto.
  forwards: IHn eq1 eq2. lia.
  auto.
Qed.


Lemma eq_trans: forall E A B C,
 eq E A B ->
 eq E B C ->
 eq E A C.
Proof.
  introv eq1 eq2. 
  eapply eq_trans_size ;eauto.
Qed.



Lemma sptype_inf: forall G mu P u A,
 P |== mu ->
 pvalue u -> 
 styping G P u Inf A -> 
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


Lemma sprinciple_typ_inf: forall G P u A,
 value u -> 
 styping G P u Inf A -> 
 principle_type u = A.
Proof.
  introv val typ.
  inverts* val; try solve[inverts* typ].
Qed.



Theorem static_ddstep_dyn_chk : forall e e' B P mu mu',
  P |== mu ->
  phi_static P ->
 dterm_static e ->
 dtyp_static B ->
 styping nil P e Chk B ->
 dstep ( e, mu) ( e', mu') -> 
 step (e, mu) ((r_e e'), mu').
Proof.
 introv wel ps ts tys typ red. gen B P.
 inductions red; intros; eauto;
 try solve[forwards*:eq_consist  H1];
 try solve[forwards*: eq_consist H0].
 - forwards h0 :  fill_static ts.
   forwards hh0: fill_chk_chk typ; auto. 
   inverts hh0.
   inverts H0.
   forwards h2: styping_typing H2.
   forwards h1: dtyping_static_preserve h2; auto.
   unfold Dtyping_static_preserve in *.
   forwards : eq_static H1; auto.
   eauto.
  -
    inverts typ. inverts H3.
    inverts H9.
    forwards* h1: styping_typing H4.
    inverts H8. inverts H11. inverts H6. inverts H5. 
    inverts H4. inverts H8.
    forwards* h2: eq_consist H4.
    forwards* h3: eq_trans H4 H3.
    forwards* h4:eq_consist h3.
    assert(styping empty P (e_anno u A0) Inf A0); eauto.
    forwards* h5: styping_typing H6.
    forwards* h6: eq_trans h3 H10.
    forwards* h7:eq_consist h6.
    forwards*: TypedReduce_progress A0 h1.
    inverts* H7.
    lets red1: H8. 
    inverts* H8.
    +
    forwards* h8: sptype_inf H5.
    forwards*: ptype_uniq H17 h8. inverts* H7.
    forwards*: TypedReduce_progress A1 h5.
    inverts* H7.
    lets red2: H8. 
    inverts* H8.
    forwards*: ptype_uniq H17 H20. inverts* H7.
    +
    forwards* h8: sptype_inf H5.
    forwards*: ptype_uniq H17 h8. inverts* H7.
  -
    inverts ts.
    inverts typ. inverts* H1.
  - inverts typ. inverts* H2.
    lets typ':H6.
    inverts* H6. inverts* H3.
    inverts* H7.
    forwards*:  sptype_inf H4.
    forwards*: eq_trans H3 H2.
    forwards*: eq_trans H6 H1.
    forwards*: eq_consist H6.
    forwards*: styping_typing typ'.
    inverts H9.
    forwards*: TypedReduce_progress A0 H11.
    forwards* h1: eq_consist H3.
    inverts* H9.
    lets H12': H12.
    inverts* H12.
    forwards*: ptype_uniq H5 H18. inverts* H9.
    forwards*: eq_consist H3.
    forwards*: ptype_uniq H5 H18. inverts* H9.
    -
    inverts typ. inverts* H2.
    forwards* typ': styping_typing H8.
    inverts H7. inverts H9. inverts* H3.
    inverts* H2. 
    inverts* H8. inverts* H3. inverts* H11.
    forwards* h1:  sptype_inf H4.
    forwards* h2: eq_trans H3 H2.
    forwards* h3: eq_sym H9. 
    forwards*: eq_trans h2 h3.
    forwards*: eq_consist H2.
    forwards* h4: eq_consist H7.
    forwards* h5: eq_consist h2.
    inverts* typ'.
    forwards*: TypedReduce_progress A1 H12.
    inverts* H13.
    lets red1: H14. 
    inverts* H14.
    +
    forwards*: ptype_uniq h1 H20. inverts* H13.
    forwards*: eq_consist H3.
    inverts H12. inverts* H17.
    assert(styping empty P (e_anno u A1) Inf A1);eauto.
    forwards* h6: styping_typing H15.
    forwards* h7:  TypedReduce_progress (store_Tlookup l P) h6.
    inverts* h7. 
    lets h9: H16. inverts H16.
    forwards* h8: ptype_uniq H26 H20. inverts* h8.
    inverts wel.
    inverts H17.
    rewrite H18 in *.
    forwards h10: H22 l. auto.
    forwards h11: principle_typ_inf h10.
    forwards*: sto_ok_value H16.
    rewrite h11 in *.
    eapply  step_set; eauto.
    forwards* h8: ptype_uniq H26 H20. inverts* h8.
    +
    forwards* h8: ptype_uniq H20 h1. inverts* h8.
Qed.


Theorem static_stepd_dyn_chk : forall G e e' B P mu mu',
P |== mu ->
  phi_static P ->
  denv_static G ->
  dterm_static e ->
 dtyp_static B ->
 styping G P e Chk B ->
 step (e, mu) ((r_e e'), mu') ->
 dstep ( e, mu) ( e', mu').
Proof.
 introv wel ps envs es ts typ red. 
 gen G B P.
 inductions red; intros; eauto;
 try solve[forwards*:dtyp_static_eq  H1];
 try solve[forwards*: dtyp_static_eq H0].
 -
   forwards h0: fill_static es.
   forwards hh1: fill_chk_chk typ; auto.
   inverts hh1.
   inverts H0.
   forwards h2: styping_typing H2. 
   forwards h1: dtyping_static_preserve h2; auto.
   unfold Dtyping_static_preserve in *.
   forwards h3: eq_static H1; auto.
   eauto.
  -
    inverts es.
    inverts typ. inverts* H5.
    inverts* H12. inverts* H2.
    inverts H3. inverts H14. inverts* H15.
    inverts H0.
    inverts H13. inverts H5.
    inverts H14.
    forwards* h1: sptype_inf H11.
    forwards*:eq_trans H5 H0.
    forwards*:eq_consist H12.
    inverts H9.
    inverts H10. inverts H14. inverts H9.
    forwards*:eq_trans H12 H17.
    forwards*:eq_consist H9.
    inverts* H8.
  -
    inverts es.
    inverts typ. inverts* H1.
  -
    inverts es.
    inverts typ. inverts* H3.
    inverts* H9. inverts* H1.
  -
    inverts es.
    inverts typ. inverts* H2.
    inverts* H10. inverts* H3.
    inverts* H0.
  -
    inverts es.
    inverts typ. inverts* H4.
    inverts* H11. inverts* H3.
    inverts* H9. inverts* H4.
    inverts* H2. inverts* H16.
    inverts H12.
    inverts H0. inverts H4.
    inverts* H16.
    forwards* h1:  sptype_inf  H4.
    forwards* h2: eq_trans H0 H2.
    forwards* h3: eq_consist h2.
    inverts H3.
    forwards*: eq_sym H18.
    forwards* h4: eq_trans h2 H3.
    forwards* h5: eq_consist h4.
    inverts H11.
    inverts wel.
    inverts H14.
    rewrite H15 in *.
    forwards*: H16.
    forwards*: sto_ok_value H11.
    forwards* h6:  principle_typ_inf  H14.
    rewrite <- h6 in *.
    inverts* H10.
    inverts* H17.
  -
    inverts es.
    inverts typ. inverts* H3.
    inverts* H7. inverts* H0.
Qed.

