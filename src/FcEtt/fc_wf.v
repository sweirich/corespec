Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.


Require Import FcEtt.tactics.

Require Import FcEtt.toplevel.


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


(* ---------------------------------------------------- *)

Lemma ann_ctx_wff_mutual :
  (forall G0 psi a A, AnnTyping G0 psi a A -> AnnCtx G0) /\
  (forall G0 psi phi,   AnnPropWff G0 psi phi -> AnnCtx G0) /\
  (forall G0 psi g p1 p2, AnnIso G0 psi g p1 p2 -> AnnCtx G0) /\
  (forall G0 psi g A B,   AnnDefEq G0 psi g A B -> AnnCtx G0) /\
  (forall G0, AnnCtx G0 -> True).
Proof.
  eapply ann_typing_wff_iso_defeq_mutual; eauto.
Qed.


Lemma AnnTyping_AnnCtx : forall G0 psi a A, AnnTyping G0 psi a A -> AnnCtx G0.
Proof. sfirstorder use:ann_ctx_wff_mutual. Qed.

Lemma AnnPropWff_AnnCtx : forall G0 psi phi,   AnnPropWff G0 psi phi -> AnnCtx G0.
Proof. sfirstorder use:ann_ctx_wff_mutual. Qed.

Lemma AnnIso_AnnCtx : forall G0 psi g p1 p2, AnnIso G0 psi g p1 p2 -> AnnCtx G0.
Proof. sfirstorder use:ann_ctx_wff_mutual. Qed.

Lemma AnnDefEq_AnnCtx : forall G0 psi g A B,   AnnDefEq G0 psi g A B -> AnnCtx G0.
Proof. sfirstorder use:ann_ctx_wff_mutual. Qed.

Hint Resolve AnnTyping_AnnCtx AnnPropWff_AnnCtx AnnIso_AnnCtx
     AnnDefEq_AnnCtx : ctx_wff.

(* Look for an extended context that we can derive information from *)
Ltac sort_inversion :=
  let h0 := fresh in
  match goal with
  | [ H : AnnTyping ([(?x,?s)] ++ ?G) _ _ |- _ ] =>
    have h0: AnnCtx (x ~ s ++ G); eauto with ctx_wff;
    inversion h0; subst; auto
  | [ H : AnnDefEq ([(?x,?s)] ++ ?G) _ _ _ |- _ ] =>
    have h0: AnnCtx (x ~ s ++ G); eauto with ctx_wff;
    inversion h0; subst; auto
  | [ H : AnnIso ([(?x,?s)] ++ ?G) _ _ _ |- _ ] =>
    have h0: AnnCtx (x ~ s ++ G); eauto with ctx_wff;
    inversion h0; subst; auto
  end.


(* ---------------------------------------------------- *)

Lemma AnnCtx_uniq G : AnnCtx G -> uniq G.
Proof. by elim=> * //=; apply uniq_cons. Qed.

Hint Resolve AnnCtx_uniq.

(* ---------------------------------------------------- *)

Hint Resolve lc_open_switch_co : lc.

Lemma lc_mutual :
  (forall G0 psi a A, AnnTyping G0 psi a A -> lc_tm a /\ lc_tm A) /\
  (forall G0 psi phi, AnnPropWff G0 psi phi -> lc_constraint phi) /\
  (forall G0 psi g p1 p2, AnnIso G0 psi g p1 p2 -> lc_constraint p1 /\ lc_constraint p2 /\ lc_co g) /\
  (forall G0 psi g A B,  AnnDefEq G0 psi g A B -> lc_tm A /\ lc_tm B /\ lc_co g) /\
  (forall G0, AnnCtx G0 -> forall x psi s , binds x (psi, s) G0 -> lc_sort s).
Proof.
  apply ann_typing_wff_iso_defeq_mutual.
  all: pre; basic_solve_n 2; split_hyp.
  all: lc_solve.
Qed.



Lemma AnnTyping_lc : forall G0 psi a A, AnnTyping G0 psi a A -> lc_tm a /\ lc_tm A.
Proof. sfirstorder use:ann_ctx_wff_mutual. Qed.

Lemma AnnPropWff_lc : forall G0 psi phi, AnnPropWff G0 psi phi -> lc_constraint phi.
Proof. sfirstorder use:ann_ctx_wff_mutual. Qed.

Lemma AnnIso_lc : forall G0 psi g p1 p2, AnnIso G0 psi g p1 p2 -> lc_constraint p1 /\ lc_constraint p2 /\ lc_co g.
Proof. sfirstorder use:ann_ctx_wff_mutual. Qed.

Lemma AnnDefEq_lc : forall G0 psi g A B,  AnnDefEq G0 psi g A B -> lc_tm A /\ lc_tm B /\ lc_co g.
Proof. sfirstorder use:ann_ctx_wff_mutual. Qed.

Lemma AnnCtx_lc : forall G0, AnnCtx G0 -> forall x psi s , binds x (psi, s) G0 -> lc_sort s.
Proof. sfirstorder use:ann_ctx_wff_mutual. Qed.

Lemma AnnTyping_lc1 : forall G psi a A, AnnTyping G psi a A -> lc_tm a.
Proof.
  intros G a A H. destruct (AnnTyping_lc H); auto.
Qed.
Lemma AnnTyping_lc2 : forall G psi a A, AnnTyping G psi a A -> lc_tm A.
  intros G a A H. destruct (AnnTyping_lc H); auto.
Qed.

Lemma AnnIso_lc1 : forall G D g p1 p2, AnnIso G D g p1 p2 -> lc_constraint p1.
Proof. intros. destruct (AnnIso_lc H); auto. Qed.
Lemma AnnIso_lc2 : forall G D g p1 p2, AnnIso G D g p1 p2 -> lc_constraint p2.
Proof. intros. destruct (AnnIso_lc H); split_hyp; auto. Qed.
Lemma AnnIso_lc3 : forall G D g p1 p2, AnnIso G D g p1 p2 -> lc_co g.
Proof. intros. destruct (AnnIso_lc H); split_hyp; auto. Qed.
Lemma AnnDefEq_lc1 : forall G D g A B,  AnnDefEq G D g A B -> lc_tm A.
Proof. intros. destruct (AnnDefEq_lc H); auto. Qed.
Lemma AnnDefEq_lc2 : forall G D g A B,  AnnDefEq G D g A B -> lc_tm B.
Proof. intros. destruct (AnnDefEq_lc H); split_hyp; auto. Qed.
Lemma AnnDefEq_lc3 : forall G D g A B,  AnnDefEq G D g A B -> lc_co g.
Proof. intros. destruct (AnnDefEq_lc H); split_hyp; auto. Qed.

Hint Resolve AnnTyping_lc1 AnnTyping_lc2 AnnIso_lc1 AnnIso_lc2 AnnIso_lc3 AnnDefEq_lc1 AnnDefEq_lc2 AnnDefEq_lc3 AnnCtx_lc : lc.


Lemma AnnToplevel_lc : forall c psi0 s, binds c (psi0, s) an_toplevel -> lc_sig_sort s.
Proof. induction AnnSig_an_toplevel.
       intros; lc_solve.
       all: intros; lc_solve_binds; split_hyp; subst; eauto with lc.
Qed.
