Require Import FcEtt.tactics.
Require Import FcEtt.utils.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.
Require Export FcEtt.labels.
Require Export FcEtt.grade_sig.
Require Import FcEtt.toplevel.
Require Import FcEtt.ext_wf.
Require Export FcEtt.pumping.
Open Scope grade_scope.

Lemma Typing_meet_ctx_l : forall G psi b B q,
    Typing G psi b B ->
    Typing (meet_ctx_l q G) psi b B.
Proof.
  scrush use: Typing_Ctx, meet_ctx_l_ctx_sub.
Qed.

Lemma typing_subsumption_mutual :
  (forall G0 psi a A, Typing G0 psi a A -> forall psi', psi <= psi' -> psi' <= q_C -> Typing G0 psi' a A) /\
  (forall G0 psi phi,   PropWff G0 psi phi -> forall psi', psi <= psi' -> psi' <= q_C -> PropWff G0 psi' phi) /\
  (forall G0 psi p1 p2, Iso G0 psi p1 p2 -> forall psi', psi <= psi' -> psi' <= q_C -> Iso G0 psi' p1 p2) /\
  (forall G0 psi phi,   DefEq G0 psi phi -> forall psi', psi <= psi' -> psi' <= q_C -> DefEq G0 psi' phi) /\
  (forall G0, Ctx G0 -> True) /\
  (forall G0 psi psi0 a b A,CDefEq G0 psi psi0 a b A -> forall psi', psi <= psi' -> psi' <= q_C -> CDefEq G0 psi' psi0 a b A).
Proof.
  apply typing_wff_iso_defeq_mutual; intros.
  (* 44 goals *)
  all : try eauto 3.
  - 


