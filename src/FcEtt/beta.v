Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.

Require Export FcEtt.ext_context_fv.

Require Import FcEtt.ext_wf.
Import ext_wf.
(*
Require Import FcEtt.fc_wf.
Import fc_wf.
*)

Require Import FcEtt.utils.
Require Export FcEtt.toplevel.
Require Import FcEtt.ett_value.

Lemma Beta_lc1 : forall a a' R, Beta a a' R -> lc_tm a.
  intros.  induction H; eauto using Value_lc, CoercedValue_lc.
Qed.

Lemma Beta_lc2 : forall a a' R, Beta a a' R -> lc_tm a'.
intros.  induction H; eauto using Value_lc, CoercedValue_lc.
- apply Value_lc in H0. inversion H0.
  apply lc_body_tm_wrt_tm; auto.
- inversion H. apply lc_body_tm_wrt_co; auto.
- apply Toplevel_lc in H. inversion H. auto.
- inversion H; subst; eauto using Value_lc, CoercedValue_lc. 
  inversion H1; subst; eauto using Value_lc.
- inversion H0; subst; eauto using Value_lc, CoercedValue_lc. 
   inversion H1; subst; eauto using Value_lc.
-  inversion H; subst; eauto using Value_lc.
  inversion H0; subst; eauto using Value_lc, CoercedValue_lc. 
  inversion H3; subst; eauto using Value_lc, CoercedValue_lc. 
Qed.

Lemma cf : forall A B (f : A -> B) (a b : A),  a = b -> f a = f b.
  intros. f_equal.
  auto.
Qed.
Lemma Beta_tm_subst : forall a a' R b x, Beta a a' R -> lc_tm b -> Beta (tm_subst_tm_tm b x a) (tm_subst_tm_tm b x a') R.
Proof.
  intros.
  destruct H.
  - simpl.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm; eauto 2.
    econstructor; eauto using tm_subst_tm_tm_lc_tm.
    apply tm_subst_tm_tm_lc_tm with (a2 := b) (x1:=x) in H; auto.
    eapply Value_tm_subst_tm_tm in H1; eauto.
  - simpl.
    rewrite tm_subst_tm_tm_open_tm_wrt_co; eauto 2.
    simpl.
    econstructor.
    apply tm_subst_tm_tm_lc_tm with (a2 := b) (x1:=x) in H; auto.
  - move: (toplevel_closed H) => h.
    simpl.
    rewrite tm_subst_tm_tm_fresh_eq; last by eauto.
    move: (first context_fv_mutual _ _ _ _ h) => Fr. simpl in Fr.
    fsetdec.
  - 
Admitted.

Lemma Beta_co_subst : forall a a' R b x, Beta a a' R -> lc_co b -> Beta (co_subst_co_tm b x a) (co_subst_co_tm b x a') R.
Proof.
  intros.
  destruct H.
  - simpl.
    rewrite co_subst_co_tm_open_tm_wrt_tm; eauto 2.
    econstructor; eauto using co_subst_co_tm_lc_tm.
    apply co_subst_co_tm_lc_tm with (g1 := b) (c1:=x) in H; auto.
    eapply Value_co_subst_co_tm in H1; eauto.
  - simpl.
    rewrite co_subst_co_tm_open_tm_wrt_co; eauto 2.
    simpl.
    econstructor.
    apply co_subst_co_tm_lc_tm with (g1 := b) (c1:=x) in H; auto.
  - move: (toplevel_closed H) => h.
    simpl.
    rewrite co_subst_co_tm_fresh_eq. eauto.
    move: (first context_fv_mutual _ _ _ _ h) => Fr. simpl in Fr.
    fsetdec.
Admitted.
