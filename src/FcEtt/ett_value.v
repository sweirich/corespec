Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.
Require Export FcEtt.ett_inf_cs.
Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.


Require Export FcEtt.ext_context_fv.

Require Import FcEtt.ext_wf.
Import ext_wf.

Require Import FcEtt.utils.
Require Export FcEtt.toplevel.


(* ------------------------------------------ *)

(* ------------------------------------------- *)

Lemma Path_subst_tm : forall F a x b R, Path F a R -> lc_tm b ->
                            Path F (tm_subst_tm_tm b x a) R.
Proof. intros. induction H; simpl; auto. econstructor; eauto.
       econstructor. apply tm_subst_tm_tm_lc_tm; auto. auto.
Qed.

Lemma Path_subst_co : forall F a c b R, Path F a R -> lc_co b ->
                            Path F (co_subst_co_tm b c a) R.
Proof. intros. induction H; simpl; auto. econstructor; eauto.
       econstructor. apply co_subst_co_tm_lc_tm; auto. auto.
Qed.

(* Values and CoercedValues *)

Lemma tm_subst_tm_tm_Value_mutual :
  (forall R v,  CoercedValue R v -> forall b x,  lc_tm b -> CoercedValue R (tm_subst_tm_tm b x v)) /\
  (forall R v, Value R v -> forall b x,  lc_tm b -> Value R (tm_subst_tm_tm b x v)).
Proof.
  apply CoercedValue_Value_mutual; simpl.
  all: try solve [inversion 1 | econstructor; eauto]; eauto.
  all: try solve [intros;
                  eauto using tm_subst_tm_tm_lc_tm,
                  tm_subst_tm_constraint_lc_constraint,
                  tm_subst_tm_co_lc_co].
  all: try solve [intros;
    constructor; eauto using tm_subst_tm_tm_lc_tm,  tm_subst_tm_constraint_lc_constraint;
    match goal with [H: lc_tm (?a1 ?a2), K : lc_tm ?b |- _ ] =>
                    move: (tm_subst_tm_tm_lc_tm _ _ x H K) => h0; auto end].

  - intros L R R1 a v H b x H0.
    econstructor; eauto.
    instantiate (1 := L \u singleton x) => x0 h0.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto.
  - intros. econstructor. apply tm_subst_tm_tm_lc_tm; auto.
    eapply Path_subst_tm; eauto. eauto.
  - intros. econstructor. eapply Path_subst_tm; eauto. eauto.
Qed.

Lemma Value_tm_subst_tm_tm :
  (forall R v b x, Value R v -> lc_tm b -> Value R (tm_subst_tm_tm b x v)).
Proof.
  intros R v b x H H0.
  apply tm_subst_tm_tm_Value_mutual; auto.
Qed.

Lemma CoercedValue_tm_subst_tm_tm :
  (forall R v b x, CoercedValue R v -> lc_tm b -> CoercedValue R (tm_subst_tm_tm b x v)).
Proof.
  intros R v b x H H0.
  destruct (tm_subst_tm_tm_Value_mutual); auto.
Qed.

(* ------------------------------------------------- *)

Lemma Value_UAbsIrrel_exists : ∀ x (a : tm) R R1,
    x `notin` fv_tm a
    → (CoercedValue R (open_tm_wrt_tm a (a_Var_f x)))
    → Value R (a_UAbs Irrel R1 a).
Proof.
  intros.
  eapply (Value_UAbsIrrel ({{x}})); eauto.
  intros.
  rewrite (tm_subst_tm_tm_intro x); eauto.
  eapply CoercedValue_tm_subst_tm_tm; auto.
Qed.
(*
Lemma Value_AbsIrrel_exists : ∀ x (A a : tm) R R1,
    x `notin` fv_tm a
    -> lc_tm A
    → (CoercedValue R (open_tm_wrt_tm a (a_Var_f x)))
    → Value R (a_Abs Irrel A R1 a).
Proof.
  intros.
  eapply (Value_AbsIrrel ({{x}})); eauto.
  intros.
  rewrite (tm_subst_tm_tm_intro x); eauto.
  eapply CoercedValue_tm_subst_tm_tm; auto.
Qed.
*)
(* ----- *)

Lemma co_subst_co_tm_Value_mutual :
  (forall R v,  CoercedValue R v -> forall b x,  lc_co b -> CoercedValue R (co_subst_co_tm b x v)) /\
  (forall R v, Value R v -> forall b x,  lc_co b -> Value R (co_subst_co_tm b x v)).
Proof.
  apply CoercedValue_Value_mutual; simpl.
  all: try solve [inversion 1 | econstructor; eauto]; eauto.
  all: try solve [intros;
                  eauto using co_subst_co_tm_lc_tm,
                  co_subst_co_constraint_lc_constraint,
                  co_subst_co_co_lc_co].
  all: try solve [intros;
    constructor; eauto using co_subst_co_tm_lc_tm,
                              co_subst_co_constraint_lc_constraint;
    match goal with [H: lc_tm (?a1 ?a2), K : lc_co ?b |- _ ] =>
                    move: (co_subst_co_tm_lc_tm _ _ x H K) => h0; auto end].
  - intros.
    pick fresh y.
    eapply Value_UAbsIrrel_exists with (x:=y).
    eapply fv_tm_tm_tm_co_subst_co_tm_notin; eauto.
    move: (H y ltac:(eauto) b x H0) => h0.
    rewrite co_subst_co_tm_open_tm_wrt_tm in h0.
    simpl in h0. auto. auto.
  - intros. econstructor. apply co_subst_co_tm_lc_tm; auto.
    eapply Path_subst_co; eauto. eauto.
  - intros. econstructor. eapply Path_subst_co; eauto. eauto.
Qed.

Lemma Value_co_subst_co_tm :
  (forall R v b x, Value R v -> lc_co b -> Value R (co_subst_co_tm b x v)).
Proof.
  intros R v b x H H0.
  apply co_subst_co_tm_Value_mutual; auto.
Qed.

Lemma CoercedValue_co_subst_co_tm :
  (forall R v b x, CoercedValue R v -> lc_co b -> CoercedValue R (co_subst_co_tm b x v)).
Proof.
  intros R v b x H H0.
  destruct (co_subst_co_tm_Value_mutual); auto.
Qed.

Lemma CoercedValue_Value_lc :
  (forall R v, CoercedValue R v -> lc_tm v) /\
  (forall R v, Value R v -> lc_tm v).
Proof. apply CoercedValue_Value_mutual; intros; auto.
Qed.


(* ------------------------------------------ *)
