
Require Export FcEtt.imports.
Require Import FcEtt.utils.
Require Export FcEtt.tactics.

Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.
Require Export FcEtt.ett_par.
Require Import FcEtt.ext_wf.
(* Require Export FcEtt.erase_syntax. *)

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".



Lemma reduction_in_one_lc : forall a a' R, reduction_in_one a a' R -> lc_tm a -> lc_tm a'.
Proof.
  induction 1; intros; lc_solve.
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
  - autorewrite with subst_open; eauto.
    econstructor; eauto using tm_subst_tm_tm_lc_tm.
    match goal with | [ H0 : Value _ _ |- _ ] =>
    eapply Value_tm_subst_tm_tm in H0; eauto end.
  - lc_subst_case x0 b0.
  - rewrite tm_subst_tm_tm_fresh_eq.
    eapply E_Axiom; eauto.
    match goal with
    | [H : binds ?c ?phi ?G |- _ ] =>
      move:  (toplevel_closed H) => h0
    end.
    show_fresh.
    fsetdec.
(*  - eapply E_Combine; auto. eapply tm_subst_tm_tm_Value_mutual in H; eauto.
  - econstructor. eapply tm_subst_tm_tm_lc_tm; eauto.
    eapply tm_subst_tm_tm_Value_mutual in H0; eauto.
  - econstructor; eapply tm_subst_tm_tm_Value_mutual in H; eauto. *)
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

Lemma Path_role_less : forall F a R, Path F a R -> exists a1 A1 R1,
                          binds F (Ax a1 A1 R1) toplevel /\ ~(SubRole R1 R).
Proof. intros F a R H. induction H; eauto.
Qed.

(* Coerced values and values are terminal. *)
Lemma no_CoercedValue_Value_reduction :
  (forall R a, CoercedValue R a -> forall b, not (reduction_in_one a b R)) /\
  (forall R a, Value R a -> forall b, not (reduction_in_one a b R)).
Proof.
  apply CoercedValue_Value_mutual; simpl; intros; eauto 2.
  all: intro NH; inversion NH; subst.
Admitted.
(*
  - eapply H; eauto.
  - inversion v.
  - eapply H; eauto.
  - contradiction.
  - pick fresh x.
    move: (H x ltac:(auto)) => h0.
    move: (H4 x ltac:(auto)) => h5.
    eapply h0; eauto.
  - inversion H0. inversion b.
    rewrite H2 in H; inversion H; subst; auto.
    inversion H2. inversion H.
  - pose (Q := H a'); contradiction.
  - inversion p.
  - inversion v.
  - pose (Q := H a'); contradiction.
  - inversion p.
  - inversion v.
Qed. *)

Lemma no_Value_reduction :
   forall R a, Value R a -> forall b, not (reduction_in_one a b R).
Proof.
  apply no_CoercedValue_Value_reduction.
Qed.

Lemma sub_Path : forall F a R1 R2, Path F a R1 -> SubRole R1 R2 ->
                        Path F a R2 \/ (exists a', reduction_in_one a a' R2).
Proof. intros. induction H.
        - destruct (sub_dec R1 R2) as [P1 | P2].
          right. exists a. eauto. left. eauto.
        - apply IHPath in H0. inversion H0 as [P1 | P2].
          left. eauto. right. inversion P2 as [a' Q].
          exists (a_App a' rho R1 b'); eauto.
        - apply IHPath in H0. inversion H0 as [P1 | P2].
          left. eauto. right. inversion P2 as [a' Q].
          exists (a_CApp a' g_Triv); eauto.
(*        - apply IHPath in H0. inversion H0 as [P1 | P2].
          left. eauto. right. inversion P2 as [a' Q].
          exists (a_Conv a' R1 g_Triv); eauto. *)
Qed.


Lemma sub_Value_mutual :
  (forall R v,  CoercedValue R v -> forall R', SubRole R R' ->
           CoercedValue R' v \/ exists a, reduction_in_one v a R') /\
  (forall R v, Value R v -> forall R', SubRole R R' ->
           Value R' v \/ exists a, reduction_in_one v a R').
Proof.
  apply CoercedValue_Value_mutual; simpl.
  all: try solve [inversion 1 | econstructor; eauto]; eauto.
  all: intros.
  - destruct (H R' H0) as [H1 | H2]. left. econstructor; auto. auto.
  - destruct (H R' H0) as [H1 | H2]. left. eapply CC; auto. right.
    inversion H2 as [a0 S]. exists (a_Conv a0 R1 g_Triv). 
Admitted.
(*
econstructor. auto.
  - destruct (H R' H0) as [H2 | H3]. left. eapply CCV; eauto.
    right. inversion H3 as [a0 S]. exists (a_Conv a0 R2 g_Triv); eauto.
  - pick fresh x. destruct (H x ltac:(auto) R' H0) as [H1 | [a0 H2]].
    left. econstructor. intros. rewrite (tm_subst_tm_tm_intro x); auto.
    apply CoercedValue_tm_subst_tm_tm; auto.
    right. pick fresh y.
    apply subst_reduction_in_one with (x := x) (b := a_Var_f y) in H2; auto.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in H2; auto.
    rewrite tm_subst_tm_tm_fresh_eq in H2; auto.
    assert (tm_subst_tm_tm (a_Var_f y) x (a_Var_f x) = a_Var_f y).
    unfold tm_subst_tm_tm; default_simp. rewrite H1 in H2.
    exists (a_UAbs Irrel R1 (close_tm_wrt_tm y (tm_subst_tm_tm (a_Var_f y) x a0))).
    apply E_AbsTerm_exists with (x := y); auto.
    apply notin_union_3; auto. rewrite fv_tm_tm_tm_close_tm_wrt_tm. auto.
    rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.
  - destruct (sub_dec R1 R') as [H1 | H2]. right. exists a; econstructor; eauto.
    left; econstructor; eauto. Unshelve. all:auto.
  - eapply sub_Path in p; eauto. destruct (H R' H0) as [P1 | P2].
    destruct p as [Q1 | Q2]. left. eauto. destruct Q2 as [a' Q].
    apply no_Value_reduction with (b := a') in P1. contradiction.
    destruct P2 as [a0 P]. right. exists (a_App a0 rho R1 b'). eauto.
  - eapply sub_Path in p; eauto. destruct (H R' H0) as [P1 | P2].
    destruct p as [Q1 | Q2]. left. eauto. destruct Q2 as [a' Q].
    apply no_Value_reduction with (b := a') in P1. contradiction.
    destruct P2 as [a0 P]. right. exists (a_CApp a0 g_Triv). eauto.
Qed. *)

Lemma sub_red_one :
  forall R R' a a', reduction_in_one a a' R -> SubRole R R' ->
                    exists a'', reduction_in_one a a'' R'.
Proof. intros. induction H; eauto.
        - pick fresh x. destruct (H1 x) as [a'' P]; auto.
          exists (a_UAbs Irrel R (close_tm_wrt_tm x a'')).
          apply E_AbsTerm_exists with (x := x).
          rewrite fv_tm_tm_tm_close_tm_wrt_tm. fsetdec.
          rewrite open_tm_wrt_tm_close_tm_wrt_tm. auto.
        - apply IHreduction_in_one in H0. inversion H0 as [a'' P].
          exists (a_App a'' rho R b); auto.
        - apply IHreduction_in_one in H0. inversion H0 as [a'' P].
          exists (a_CApp a'' g_Triv); auto.
        - eapply sub_Value_mutual in H1; eauto.
          inversion H1. exists (open_tm_wrt_tm v a); auto.
          inversion H2 as [a'' P]. exists (a_App a'' rho R a); auto.
(*        - apply IHreduction_in_one in H0. inversion H0 as [a'' P].
          exists (a_Conv a'' R g_Triv); auto.
        - eapply sub_Value_mutual in H; eauto. inversion H as [H2 | H3].
          exists (a_Conv v R2 g_Triv). eapply E_Combine; eauto.
          inversion H3 as [a0 S]. exists (a_Conv a0 R2 g_Triv). eauto.
        - eapply sub_Value_mutual in H1; eauto. inversion H1 as [H2 | H3].
          exists (a_Conv (a_App v1 rho R1 (a_Conv b R g_Triv)) R g_Triv).
          econstructor; eauto. inversion H3 as [a0 S].
          exists (a_App a0 rho R1 b). econstructor. auto. auto.
        - eapply sub_Value_mutual in H; eauto. inversion H as [H2 | H3].
          exists (a_Conv (a_CApp v1 g_Triv) R g_Triv). econstructor; eauto.
          inversion H3 as [a0 S]. exists (a_CApp a0 g_Triv).
          econstructor. auto. *)
Qed.

Ltac CoercedValue_no_red :=
     match goal with
      | [ H : CoercedValue ?R ?a,
          R : reduction_in_one ?a ?a' ?R |- _ ] =>
        eapply no_CoercedValue_Value_reduction with (b := a') in H;
        contradiction; fail
     end.

(* The reduction relation is deterministic *)
Lemma reduction_in_one_deterministic :
  forall a a1 R, reduction_in_one a a1 R -> forall a2, reduction_in_one a a2 R -> a1 = a2.
Proof.
  intros a a1 R H.
  induction H; intros a2 h0.
  all: inversion h0; subst.
  (* already equal *)
  all: auto.

  (* follows by induction *)
  all: try solve [erewrite IHreduction_in_one; eauto].

  (* impossible case, reduction of value *)
  all: try solve [(have: False by eapply no_Value_reduction; eauto); done].
  all: try CoercedValue_no_red.

  (* TODO: guard the number of subgoals (2)? *)

  - pick fresh x.
    move: (H5 x ltac:(auto)) => h7.
    move: (H0 x ltac:(auto)) => h1.
    apply h1 in h7.
    apply open_tm_wrt_tm_inj in h7; eauto. rewrite h7. auto.
  - inversion H.
  - inversion H1.
  - have: (Ax a A R = Ax a2 A0 R2). eapply binds_unique; eauto using uniq_toplevel.
    move => h; inversion h; done.
Qed.
