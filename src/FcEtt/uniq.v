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

Lemma Grade_uniq : forall P psi a, Grade P psi a -> uniq P.
Proof. intros; induction H; eauto;
       pick fresh x; repeat spec x;
       match goal with [ H2 : uniq ([_] ++ _) |- _ ] => inversion H2; auto end.
Qed.

Lemma CEq_GEq_CoGEq_uniq : 
  (forall P psi psi0 a b,
  CEq P psi psi0 a b -> uniq P) /\
  (forall P psi a b,
  GEq P psi a b -> uniq P) /\
  (forall P psi phi1 phi2,
  CoGEq P psi phi1 phi2 -> uniq P).
Proof. 
  eapply CEq_GEq_mutual.
  all: intros; eauto.
  all: try (pick fresh x; spec x; solve_uniq).
Qed.

Lemma CEq_uniq : forall P phi phi0 a b,
  CEq P phi phi0 a b -> uniq P.
Proof. eapply CEq_GEq_CoGEq_uniq. Qed.
Lemma GEq_uniq :
  (forall P phi a b,
  GEq P phi a b -> uniq P).
Proof. eapply CEq_GEq_CoGEq_uniq. Qed.
Lemma CoGEq_uniq :
  (forall P psi phi1 phi2,
  CoGEq P psi phi1 phi2 -> uniq P).
Proof. eapply CEq_GEq_CoGEq_uniq. Qed.


Lemma Par_uniq_mutual : 
  (forall P psi a b, Par P psi a b -> uniq P) /\ 
    (forall P psi phi1 phi2, ParProp P psi phi1 phi2 -> uniq P) /\
  (forall P psi psi0 a b, CPar P psi psi0 a b -> uniq P) /\ 
  (forall P psi psi0 phi1 phi2, CParProp P psi psi0 phi1 phi2 -> uniq P).
Proof. apply Par_tm_constraint_mutual; intros; eauto.
       eapply Grade_uniq; eauto. 
       pick fresh x; spec x; solve_uniq.

       eapply Grade_uniq; eauto. 
       pick fresh x; spec x; solve_uniq.

       Unshelve.
       auto.
Qed.

Lemma Par_uniq : forall P psi a b, Par P psi a b -> uniq P.
Proof.
  sauto use : Par_uniq_mutual.
Qed.

Lemma CPar_uniq : (forall P psi phi1 phi2, ParProp P psi phi1 phi2 -> uniq P).
Proof.
  sauto use : Par_uniq_mutual.
Qed.

Lemma ParProp_uniq : (forall P psi psi0 a b, CPar P psi psi0 a b -> uniq P).
Proof.
  sauto use : Par_uniq_mutual.
Qed.


Lemma CParProp_uniq : (forall P psi psi0 phi1 phi2, CParProp P psi psi0 phi1 phi2 -> uniq P).
Proof.
  sauto use : Par_uniq_mutual.
Qed.

Lemma MultiPar_uniq : forall P psi a b, multipar P psi a b -> uniq P.
Proof. 
  hauto lq: on use: Par_uniq inv: multipar.
Qed.
