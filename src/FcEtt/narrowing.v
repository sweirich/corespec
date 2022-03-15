Require Export FcEtt.imports.
Require Export FcEtt.tactics.
Require Export FcEtt.labels. 
Require Export FcEtt.ett_ind.
Require Export FcEtt.uniq. 
Require Import FcEtt.ett_ind.

Set Implicit Arguments.
Open Scope grade_scope.







Lemma Grade_narrowing :
  (forall P psi a, Grade P psi a -> forall P', P_sub P' P -> Grade P' psi a) /\
  (forall P psi psi0 a, CGrade P psi psi0 a -> forall P', P_sub P' P -> CGrade P' psi psi0 a) /\
  (forall P psi phi, CoGrade P psi phi  -> forall P', P_sub P' P -> CoGrade P' psi phi).
Proof. 
  apply CGrade_Grade_mutual.
  all : intros; eauto using P_sub_uniq1.
  all: try solve [fresh_apply_Grade x; eauto;
    repeat spec x;
    qauto l: on ctrs: P_sub use: q_leb_refl].
  - (* Var *)
    hauto lq: on use: P_sub_binds, q_leb_trans, P_sub_uniq1 ctrs: Grade.
Qed.

Lemma CEq_GEq_narrowing : 
  (forall P psi psi0 a b,
  CEq P psi psi0 a b -> forall P', P_sub P' P -> CEq P' psi psi0 a b) /\
  (forall P psi a b,
  GEq P psi a b -> forall P', P_sub P' P -> GEq P' psi a b) /\
  (forall P psi phi1 phi2,
   CoGEq P psi phi1 phi2 -> forall P', P_sub P' P -> CoGEq P' psi phi1 phi2).
Proof. 
  apply CEq_GEq_mutual.
  all: intros; eauto using P_sub_uniq1.
  all: try solve [fresh_apply_GEq x; eauto;
    repeat spec x;
    qauto l: on ctrs: P_sub use: q_leb_refl] .
  - hauto lq: on use: P_sub_binds, q_leb_trans, P_sub_uniq1 ctrs: GEq.
Qed.

Lemma GEq_narrowing : forall P phi a b,
  GEq P phi a b -> forall P', P_sub P' P -> GEq P' phi a b.
Proof. apply CEq_GEq_narrowing; eauto. Qed.

Lemma CEq_narrowing : forall P psi psi0 a b,
    CEq P psi psi0 a b -> forall P', P_sub P' P -> CEq P' psi psi0 a b.
Proof. hauto use: CEq_GEq_narrowing. Qed.

Lemma CoGEq_narrowing : forall P psi phi1 phi2,
   CoGEq P psi phi1 phi2 -> forall P', P_sub P' P -> CoGEq P' psi phi1 phi2.
Proof. hauto use: CEq_GEq_narrowing. Qed.

Lemma Par_narrowing : 
  (  forall P1 psi a b, Par P1 psi a b -> forall P2, P_sub P2 P1 -> Par P2 psi a b) /\
  (  forall P1 psi phi1 phi2, ParProp P1 psi phi1 phi2 -> forall P2, P_sub P2 P1 -> ParProp P2 psi phi1 phi2) /\
  (  forall P1 psi psi0 a b, CPar P1 psi psi0 a b -> forall P2, P_sub P2 P1 -> CPar P2 psi psi0 a b) /\
  (  forall P1 psi psi0 phi1 phi2, CParProp P1 psi psi0 phi1 phi2 -> forall P2, P_sub P2 P1 -> CParProp P2 psi psi0 phi1 phi2).
Proof. 
  apply Par_tm_constraint_mutual.
  all : intros; pick fresh x;
    try hauto
          use:Grade_narrowing, GEq_narrowing, CPar_Nleq, P_sub_uniq1, q_leb_refl
          ctrs: P_sub, Par, CPar,ParProp,CParProp.
  apply Par_Pi with (L := dom P2 \u dom P \u L); qauto l: on use: q_leb_refl ctrs: P_sub.
  apply Par_CPi with (L := dom P2 \u dom P \u L); qauto l: on use: q_leb_refl ctrs: P_sub.
Qed.
(* for the record: the coqhammer+coq version I'm using: 1.3.2+8.15 *)
