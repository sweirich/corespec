Require Export FcEtt.imports.
Require Export FcEtt.tactics.
Require Export FcEtt.labels.
Require Import FcEtt.ett_ind.

Set Implicit Arguments.
Open Scope grade_scope.

Lemma P_sub_uniq1 : forall P P', P_sub P P' -> uniq P.
Proof. intros. induction H; eauto. Qed.

Lemma P_sub_uniq2 : forall P P', P_sub P P' -> uniq P'.
Proof. intros. induction H; eauto. Qed.

Lemma ctx_sub_uniq : forall (W1 W2 : context), ctx_sub W2 W1 -> uniq W1 -> uniq W2.
Proof.
  induction 1; intros; eauto;
  destruct_uniq;
  specialize (IHctx_sub ltac:(auto));
  solve_uniq.
Qed.

Arguments ctx_sub_uniq {_} {_}.

Lemma ECtx_uniq : forall P, ECtx P -> uniq P.
Proof.
  induction 1; sfirstorder.
Qed.

Lemma Grade_uniq : forall P psi a, Grade P psi a -> uniq P.
Proof. intros; induction H; eauto;
         pick fresh y; repeat spec y; sauto lq:on use:ECtx_uniq.
Qed.

Lemma Grade_ECtx : forall P psi a, Grade P psi a -> ECtx P.
Proof. intros; induction H; eauto;
         pick fresh y; repeat spec y; sauto lq:on.
Qed.

Lemma CEq_GEq_CoGEq_ECtx : 
  (forall P psi psi0 a b,
  CEq P psi psi0 a b -> ECtx P) /\
  (forall P psi a b,
  GEq P psi a b -> ECtx P) /\
  (forall P psi phi1 phi2,
  CoGEq P psi phi1 phi2 -> ECtx P).
Proof. 
  eapply CEq_GEq_mutual.
  all: intros; eauto.
  all: try (pick fresh x; spec x; hauto lq:on inv:ECtx).
Qed.

Lemma CEq_ECtx : forall P phi phi0 a b,
  CEq P phi phi0 a b -> ECtx P.
Proof. eapply CEq_GEq_CoGEq_ECtx. Qed.
Lemma GEq_ECtx :
  (forall P phi a b,
  GEq P phi a b -> ECtx P).
Proof. eapply CEq_GEq_CoGEq_ECtx. Qed.
Lemma CoGEq_ECtx :
  (forall P psi phi1 phi2,
  CoGEq P psi phi1 phi2 -> ECtx P).
Proof. eapply CEq_GEq_CoGEq_ECtx. Qed.


Lemma Par_ECtx_mutual : 
  (forall P psi a b, Par P psi a b -> ECtx P) /\ 
    (forall P psi phi1 phi2, ParProp P psi phi1 phi2 -> ECtx P) /\
  (forall P psi psi0 a b, CPar P psi psi0 a b -> ECtx P) /\ 
  (forall P psi psi0 phi1 phi2, CParProp P psi psi0 phi1 phi2 -> ECtx P).
Proof. apply Par_tm_constraint_mutual; intros; eauto using Grade_ECtx.
       all : solve [pick fresh x; spec x; hauto lq:on inv:ECtx].
Qed.

Lemma Par_ECtx : forall P psi a b, Par P psi a b -> ECtx P.
Proof.
  sfirstorder use : Par_ECtx_mutual.
Qed.

Lemma CPar_ECtx : (forall P psi phi1 phi2, ParProp P psi phi1 phi2 -> ECtx P).
Proof.
  sfirstorder use : Par_ECtx_mutual.
Qed.

Lemma ParProp_ECtx : (forall P psi psi0 a b, CPar P psi psi0 a b -> ECtx P).
Proof.
  sfirstorder use : Par_ECtx_mutual.
Qed.


Lemma CParProp_ECtx : (forall P psi psi0 phi1 phi2, CParProp P psi psi0 phi1 phi2 -> ECtx P).
Proof.
  sfirstorder use : Par_ECtx_mutual.
Qed.

Lemma MultiPar_ECtx : forall P psi a b, multipar P psi a b -> ECtx P.
Proof. 
  hauto lq: on use: Par_ECtx inv: multipar.
Qed.
