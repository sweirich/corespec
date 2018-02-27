
Require Export FcEtt.imports.
Require Import FcEtt.utils.
Require Export FcEtt.tactics.

Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.
Require Export FcEtt.ett_par.
Require Import FcEtt.ext_wf.
Require Export FcEtt.ett_value.
Require Import FcEtt.ett_path.

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Lemma beta_lc : forall a b R, Beta a b R -> lc_tm a -> lc_tm b.
Proof. induction 1; intros; lc_solve.
Qed.

Lemma reduction_in_one_lc : forall a a' R, reduction_in_one a a' R -> lc_tm a -> lc_tm a'.
Proof.
   induction 1; intros; try (eapply beta_lc; eauto 1; fail); lc_solve.
Qed.

(* ------------------------------------------------------------ *)

(* Tactics for substitution proofs. *)

Ltac subst_helper x x0 b0 :=
  replace (a_Var_f x) with (tm_subst_tm_tm b0 x0 (a_Var_f x));
  [idtac| rewrite tm_subst_tm_tm_var_neq; auto];
  replace (g_Var_f x) with (tm_subst_tm_co b0 x0 (g_Var_f x));
  [idtac| simpl; auto];
  try (rewrite <- tm_subst_tm_tm_open_tm_wrt_co; eauto);
  try (rewrite <- tm_subst_tm_tm_open_tm_wrt_co; eauto);
  try (rewrite <- tm_subst_tm_tm_open_tm_wrt_tm; eauto);
  try (rewrite <- tm_subst_tm_tm_open_tm_wrt_tm; eauto);
  eauto using tm_subst_tm_tm_lc_tm.

(* Most of the substitution cases below are about
   showing that the term is locally closed after the substiution.
   This tactic takes care of that argument.
*)

Ltac lc_subst_case x0 b0  :=
  let x:= fresh in
  lc_inversion x; subst;
  try (rewrite tm_subst_tm_tm_open_tm_wrt_tm; eauto);
  try (rewrite tm_subst_tm_tm_open_tm_wrt_co; eauto);

  econstructor; eauto using Value_lc,
                      tm_subst_tm_tm_lc_tm, tm_subst_tm_co_lc_co,
                tm_subst_tm_constraint_lc_constraint;
    apply_lc_exists x;
      eauto using tm_subst_tm_tm_lc_tm, tm_subst_tm_co_lc_co,
              Value_lc, tm_subst_tm_constraint_lc_constraint;
    subst_helper x x0 b0.

(* ------------------------------------------------- *)

Lemma subst_beta : forall a a' R,
  Beta a a' R -> forall b x, lc_tm b ->
  Beta (tm_subst_tm_tm b x a)
                   (tm_subst_tm_tm b x a') R.
Proof. intros a a' R H. induction H; intros b0 x0 LC; simpl.
        - autorewrite with subst_open; eauto.
          econstructor; eauto using tm_subst_tm_tm_lc_tm.
          eapply Value_tm_subst_tm_tm with (x := x0) in H0; eauto.
        - lc_subst_case x0 b0.
        - rewrite tm_subst_tm_tm_fresh_eq.
          econstructor; eauto.
          pose (P := toplevel_closed H). show_fresh. fsetdec.
        - econstructor; eauto with lngen lc. apply Path_subst; auto.
        - eapply Beta_PatternFalse; eauto with lngen lc.
          apply Value_tm_subst_tm_tm; auto. intro. apply H3.
          eapply subst_Path; eauto.
Qed.

Lemma subst_reduction_in_one : forall a a' R,
  reduction_in_one a a' R -> forall b x, lc_tm b ->
  reduction_in_one (tm_subst_tm_tm b x a)
                   (tm_subst_tm_tm b x a') R.
Proof.
  intros a a' R H. induction H; intros b0 x0 LC;
                   simpl; eauto using tm_subst_tm_tm_lc_tm,
                          tm_subst_tm_co_lc_co.
  - eapply (E_AbsTerm (L \u {{x0}})); eauto. intros x Fr.

    subst_helper x x0 b0.
  - eapply E_Prim. eapply subst_beta; eauto.
Qed.


Lemma E_AbsTerm_exists : ∀ x (a a' : tm) R R',
    x `notin` (fv_tm_tm_tm a \u fv_tm_tm_tm a') ->
     reduction_in_one (open_tm_wrt_tm a (a_Var_f x))
                       (open_tm_wrt_tm a' (a_Var_f x)) R'
    → reduction_in_one (a_UAbs Irrel R a) (a_UAbs Irrel R a') R'.
Proof.
  intros.
  eapply (E_AbsTerm ({{x}})).
  intros.
  rewrite (tm_subst_tm_tm_intro x); auto.
  rewrite (tm_subst_tm_tm_intro x a'); auto.
  eapply subst_reduction_in_one; auto.
Qed.

Lemma no_Value_reduction : forall R a, Value R a ->
          forall b, not (reduction_in_one a b R).
Proof. intros R a H. induction H; simpl; intros; eauto 2.
  all: intro NH; inversion NH; subst.
  all: try (inversion H1; fail).
  all: try (inversion H0; fail).
  all: try solve [eapply no_Path_reduction; eauto 1].
  - inversion H.
  - pick fresh x.
    move: (H0 x ltac:(auto)) => h0.
    move: (H5 x ltac:(auto)) => h5.
    eapply h0; eauto.
Qed.

Lemma sub_Value :
  forall R v, Value R v -> forall R', SubRole R R' ->
           Value R' v \/ exists a, reduction_in_one v a R'.
Proof. intros R v H. induction H; simpl; auto. all: intros.
  - pick fresh x. destruct (H0 x ltac:(auto) R' H1) as [H2 | [a0 H3]].
    left. econstructor. intros. rewrite (tm_subst_tm_tm_intro x); auto.
    apply Value_tm_subst_tm_tm; auto.
    right. pick fresh y.
    apply subst_reduction_in_one with (x := x) (b := a_Var_f y) in H3; auto.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in H3; auto.
    rewrite tm_subst_tm_tm_fresh_eq in H3; auto.
    assert (tm_subst_tm_tm (a_Var_f y) x (a_Var_f x) = a_Var_f y).
    unfold tm_subst_tm_tm; default_simp. rewrite H2 in H3.
    exists (a_UAbs Irrel R1 (close_tm_wrt_tm y (tm_subst_tm_tm (a_Var_f y) x a0))).
    apply E_AbsTerm_exists with (x := y); auto.
    apply notin_union_3; auto. rewrite fv_tm_tm_tm_close_tm_wrt_tm. auto.
    rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.
  - edestruct sub_Path; eauto 3.
    Unshelve. all: auto.
Qed.


Lemma nsub_Value :
  forall R v, Value R v -> forall R', SubRole R' R -> Value R' v.
Proof. intros R v H. induction H; simpl; auto. all: intros.
  - pick fresh x. eapply Value_UAbsIrrel with (L := L). intros. eauto.
  - eapply nsub_Path in H0; eauto.
Qed.




(* This lemma is not true because of AbsTerm.  A \-x.e may or 
   may not be a value depending on the role. *)
Lemma sub_beta_same :
      forall R R' a a', Beta a a' R -> SubRole R R' -> Beta a a' R'.
Proof. 
Abort.


Lemma sub_Beta :
      forall R R' a a', Beta a a' R -> SubRole R R' -> exists a'', reduction_in_one a a'' R'.
Proof. 
  intros. induction H; eauto. 
  eapply sub_Value in H1; eauto.
  inversion H1; clear H1.
  - eexists. eauto.
  - destruct H2; subst. 
    eexists. eapply E_AppLeft; eauto.
Qed.

Lemma sub_red_one :
  forall R R' a a', reduction_in_one a a' R -> 
               SubRole R R' ->
               exists a'', reduction_in_one a a'' R'.
Proof. intros. induction H; eauto.
       - (* AbsTerm *)
         pick fresh x. move: (H1 x ltac:(auto) H0) => [a'' r].
         eexists (a_UAbs Irrel R (close_tm_wrt_tm x a'')). 
         eapply E_AbsTerm_exists with(x:=x);
         autorewrite with lngen; auto.
       - destruct (IHreduction_in_one H0) as [a'' r].
         eexists. eauto.
       - destruct (IHreduction_in_one H0) as [a'' r].
         eexists. eauto.
       - destruct (sub_Beta H H0) as [a'' r].
         eexists. eauto.
Qed.

(* This does not hold in E_AppLeft case. *)
Lemma nsub_red_one :
  forall R R' a a', reduction_in_one a a' R -> 
               SubRole R' R -> Value R' a \/
               exists a'', reduction_in_one a a'' R'.
Proof.
Abort.

Ltac Value_no_red :=
     match goal with
      | [ H : Value ?R ?a,
          R : reduction_in_one ?a ?a' ?R |- _ ] =>
        eapply no_Value_reduction with (b := a') in H;
        contradiction; fail
     end.

(* The reduction relation is deterministic *)
Lemma Beta_deterministic :
  forall a a1 R, Beta a a1 R -> forall a2, Beta a a2 R -> a1 = a2.
Proof.
  intros  a a1 R H.
  induction H; intros a2 h0.
  all: inversion h0; subst.
  all: auto.
  have: (Ax a A R = Ax a2 A0 R2). eapply binds_unique; eauto using uniq_toplevel.
    move => h; inversion h; done.
  contradiction. contradiction.
Qed.

(* The reduction relation is deterministic *)
Lemma reduction_in_one_deterministic :
  forall a a1 R, reduction_in_one a a1 R -> forall a2, reduction_in_one a a2 R -> a1 = a2.
Proof.
  intros a a1 R H.
  induction H; intros a2 h0.
  all: inversion h0; subst.

  (* two beta reductions *)
  all: try solve [eapply Beta_deterministic; eauto 1].
  (* invert other beta reductions *)
  all: try match goal with [ H1 : Beta ?a ?b ?R |- _ ] => inversion H1; subst end.
  (* follows by induction *)
  all: try solve [erewrite IHreduction_in_one; eauto 1].

  (* impossible case, reduction of value *)
  all: try solve [(have: False by eapply no_Value_reduction; eauto 1); done].
  all: try solve [(have: False; try done; inversion H; inversion H1)].
  all: try solve [(have: False; try done; inversion H0; inversion H1)].

  (* AbsTerm *)
  - pick fresh x.
    move: (H5 x ltac:(auto)) => h7.
    move: (H0 x ltac:(auto)) => h1.
    apply h1 in h7.
    apply open_tm_wrt_tm_inj in h7; eauto. rewrite h7. auto.
  - apply Value_Path in H12. apply no_Value_reduction in H1; eauto.
    inversion H1.
  - apply Value_Path in H12. apply no_Value_reduction in H2; eauto.
    inversion H2.
Qed.
