
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
Require Import FcEtt.ett_match.
Require Import FcEtt.beta.
Require Import FcEtt.ett_rename.
Import Omega.


Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".


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
  - eapply E_Prim. eapply Beta_tm_subst; eauto.
Qed.


Lemma E_AbsTerm_exists : ∀ x (a a' : tm) R,
    x `notin` (fv_tm_tm_tm a \u fv_tm_tm_tm a') ->
     reduction_in_one (open_tm_wrt_tm a (a_Var_f x))
                       (open_tm_wrt_tm a' (a_Var_f x)) R
    → reduction_in_one (a_UAbs Irrel a) (a_UAbs Irrel a') R.
Proof.
  intros.
  eapply (E_AbsTerm ({{x}})).
  intros.
  rewrite (tm_subst_tm_tm_intro x); auto.
  rewrite (tm_subst_tm_tm_intro x a'); auto.
  eapply subst_reduction_in_one; auto.
Qed.



Lemma not_ValuePath_a_Star : forall F, ValuePath a_Star F -> False.
Proof. intros. dependent induction H. Qed.
Lemma not_ValuePath_a_Pi : forall F rho A B, ValuePath (a_Pi rho A B) F -> False.
Proof. intros. dependent induction H. Qed.
Lemma not_ValuePath_a_CPi : forall F phi B, ValuePath (a_CPi phi B) F -> False.
Proof. intros. dependent induction H. Qed.
Lemma not_ValuePath_a_UAbs : forall rho a F, ValuePath (a_UAbs rho a) F -> False.
Proof. intros. dependent induction H. Qed.
Lemma not_ValuePath_a_UCAbs : forall a F, ValuePath (a_UCAbs a) F -> False.
Proof. intros. dependent induction H. Qed.


Lemma not_CasePath_a_Star : forall F R, CasePath R a_Star F -> False.
Proof. intros. inversion H; eauto using not_ValuePath_a_Star. Qed.
Lemma not_CasePath_a_Pi : forall F R rho A B, CasePath R (a_Pi rho A B) F -> False.
Proof. intros. inversion H; eauto using not_ValuePath_a_Pi. Qed.
Lemma not_CasePath_a_CPi : forall F R phi B, CasePath R (a_CPi phi B) F -> False.
Proof. intros. inversion H; eauto using not_ValuePath_a_CPi. Qed.
Lemma not_CasePath_a_UAbs : forall R rho a F, CasePath R (a_UAbs rho a) F -> False.
Proof. intros. inversion H; eauto using not_ValuePath_a_UAbs. Qed. 
Lemma not_CasePath_a_UCAbs : forall R a F, CasePath R (a_UCAbs a) F -> False.
Proof. intros. inversion H; eauto using not_ValuePath_a_UCAbs. Qed. 

Ltac invert_Path := 
  match goal with 
    [ H1 : CasePath ?R ?a ?F |- _ ] =>
    inversion H1 end;
  match goal with 
    [ H2 : ValuePath ?a ?F |- _ ] => 
    inversion H2 end.

(* Values do not Beta reduce *)
Lemma no_Value_Beta : forall R a, Value R a ->  forall b, not (Beta a b R).
Proof. 
  intros R a H b Hb. 
  induction Hb; simpl; intros; eauto.
  - inversion H.
    invert_Path; eapply not_ValuePath_a_UAbs; eauto.
  - inversion H.
    invert_Path; eapply not_ValuePath_a_UCAbs; eauto.
  - inversion H; subst;
      try solve [match goal with [ H2 : MatchSubst ?a _ _ _ |- _ ] => inversion H2 end].
    eapply CasePath_ax_par_contr; eauto 1.
  - inversion H.
    invert_Path.
  - inversion H.
    invert_Path.
Qed.

Lemma no_Value_reduction : forall R a, Value R a ->
          forall b, not (reduction_in_one a b R).
Proof. 
  intros R a H.
  move=> b RR.
  induction RR.
  - inversion H. autofresh. auto.
    eapply not_CasePath_a_UAbs; eauto. 
  - eapply IHRR. 
    match goal with 
      [ H : Value ?R ?a |- _ ] =>
      inversion H; eapply Value_Path with (F:=F); subst end.
    invert_Path; eauto.
  - eapply IHRR. 
    match goal with 
      [ H : Value ?R ?a |- _ ] =>
      inversion H; eapply Value_Path with (F:=F); subst end.
    invert_Path; eauto.
  - inversion H.
    invert_Path; eauto.
  - eapply no_Value_Beta; eauto.
Qed.

(* ---- changing the role could cause a value to step -------------*)

Lemma tm_subst_tm_tm_id : forall x b1, 
   tm_subst_tm_tm (a_Var_f x) x b1 = b1.
Proof. 
  intros.
  rewrite tm_subst_tm_tm_spec.
  rewrite open_tm_wrt_tm_close_tm_wrt_tm.
  auto.
Qed.

Lemma tm_pattern_agree_lc2 : 
  forall a p, tm_pattern_agree a p -> lc_tm p.
Proof. induction 1; eauto. Qed.

Lemma subtm_pattern_agree_step : forall p b A R1 Rs R a F, 
  subtm_pattern_agree a p
  -> ValuePath a F
  -> binds F (Ax p b A R1 Rs) toplevel
  -> SubRole R1 R
  -> exists a', reduction_in_one a a' R.
Proof. 
  induction 1;
  move=> SPA M SR.
  + move: (toplevel_inversion M) => [W [G [B h]]].
    split_hyp. subst.
    have LCb: lc_tm b by eauto using Typing_lc1.
    have Pp: Pattern p by eapply axiom_pattern; eauto.
    set (D := fv_tm_tm_tm a `union` fv_tm_tm_tm p).
    move: (rename_Rename D Pp LCb) => RN.
    set b' := (rename p b D).1.2 in RN.
    move: (tm_pattern_agree_rename_inv_1 H RN) => AG.
    have LCb' : lc_tm b'. eapply Rename_lc4; eauto. 
    move: (MatchSubst_exists AG LCb') => [b'' MS].
    eexists.
    eapply E_Prim.
    eapply Beta_Axiom; eauto 1.
  + inversion SPA. subst.
    destruct IHsubtm_pattern_agree; auto.
    exists (a_App x nu a2).
    eapply E_AppLeft; auto.
  + inversion SPA. subst.
    destruct IHsubtm_pattern_agree; auto.
    exists (a_CApp x g_Triv); auto.
Qed.

Lemma sub_CasePath : forall R a F, CasePath R a F ->
  forall R' : role, 
  SubRole R R' ->
  CasePath R' a F \/ (∃ a0 : tm, reduction_in_one a a0 R').
Proof.
  intros R a F H. inversion H; eauto. subst. 
  intros R' SR.
  destruct (sub_dec R1 R').
  - (* have R <: R1 <: R', so could step if the pattern matches *)
    destruct (subtm_pattern_agree_dec p (ValuePath_lc H0)).
    + right. 
      eapply subtm_pattern_agree_step; eauto.
    + left.
      eauto.
  - (* have R <: R' <: R1 *)
    left.
    eapply CasePath_Const; eauto.
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
    exists (a_UAbs Irrel (close_tm_wrt_tm y (tm_subst_tm_tm (a_Var_f y) x a0))).
    apply E_AbsTerm_exists with (x := y); auto.
    apply notin_union_3; auto. rewrite fv_tm_tm_tm_close_tm_wrt_tm. auto.
    rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.
  - destruct (sub_CasePath H H0).
    left. eauto.
    right. eauto. 
Unshelve. all: auto.
Qed.

(* ----------------------------------- *)

Lemma nsub_CasePath :
  forall R v F, CasePath R v F -> forall R', SubRole R' R -> CasePath R' v F.
Proof.
  move=> R v F H. 
  inversion H; subst; intros R' SR.
  - eauto.
  - eauto.
  - eauto.
Qed.

Lemma nsub_Value :
  forall R v, Value R v -> forall R', SubRole R' R -> Value R' v.
Proof.
  intros R v H. induction H; simpl; auto. 
  all: intros.
  - pick fresh x. eapply Value_UAbsIrrel with (L := L). intros. eauto.
  - econstructor. eapply nsub_CasePath; eauto.
Qed.



(* This lemma is not true because of Paths. Raising the Role could cause 
   an axiom to trigger. *)
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
         eexists (a_UAbs Irrel (close_tm_wrt_tm x a'')). 
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



Ltac invert_MatchSubst := 
  match goal with 
  | [ H : MatchSubst ?a ?a0 ?b1 ?b2 |- _ ] => 
    inversion H; subst; clear H
  end.


(* The reduction relation is deterministic *)
Lemma Beta_deterministic :
  forall a a1 R, Beta a a1 R -> forall a2, Beta a a2 R -> a1 = a2.
Proof.
  intros  a a1 R H.
  induction H; intros a2 h0.
  all: inversion h0; subst.
  all: auto.
  all: try solve [invert_MatchSubst; invert_MatchSubst].
  all: try solve [contradiction].
  - pattern_head.
    pose (P := tm_pattern_agree_rename_inv_2 (MatchSubst_match H1) H0).
    pattern_head_tm_agree. rewrite U in U1. inversion U1; subst.
    axioms_head_same.
    pose (P1 := axiom_body_fv_in_pattern H).
     eapply MatchSubst_Rename_preserve. eauto. eapply H0. eauto.
     eapply union_s_m. eauto. eapply AtomSetProperties.union_subset_3.
     eauto. auto. eapply union_s_m. eauto.
     eapply AtomSetProperties.union_subset_3.
     eauto. auto. eapply uniq_atoms_toplevel. eauto. auto. auto.
  - (* two pattern matching *)
    move: (ApplyArgs_applyArgs H1) => h1.
    move: (ApplyArgs_applyArgs H12) => h2.
    rewrite h1 in h2. subst.
    auto.
Qed.

(* If we match subst against an application, it must headed by a value. *)
Lemma BetaAxiom_a_App_only : forall F p b0 A R0 Rs p1 b1 D' a2 a nu b R1
  (H2 : binds F (Ax p b0 A R0 Rs) toplevel)
  (H3 : Rename p b0 p1 b1 (union (fv_tm_tm_tm (a_App a nu b)) (fv_tm_tm_tm p)) D')
  (H4 : MatchSubst (a_App a nu b) p1 b1 a2)
  (H5 : SubRole R0 R1),
  Value R1 a.
Proof.
  intros. 
  move: (MatchSubst_match H4) => h4.
  eapply Value_Path with (F:=F).
  eapply CasePath_UnMatch; eauto.
  + inversion h4; subst. eapply tm_pattern_agree_ValuePath; eauto.
    eapply tm_subpattern_agree_sub_app. econstructor.
    eapply Rename_tm_pattern_agree; eauto. 
    eapply tm_pattern_agree_ValuePath; eauto.
    eapply tm_subpattern_agree_sub_app. econstructor.
    eapply Rename_tm_pattern_agree; eauto.
  + move: (tm_pattern_agree_rename_inv_2 h4 H3) => h5. 
    intro. eapply subtm_pattern_agree_app_contr; eauto.
Qed.

Lemma BetaAxiom_a_CApp_only : forall F p b0 A R0 Rs p1 b1 D' a2 a  R1
  (H2 : binds F (Ax p b0 A R0 Rs) toplevel)
  (H3 : Rename p b0 p1 b1 (union (fv_tm_tm_tm (a_CApp a g_Triv)) (fv_tm_tm_tm p)) D')
  (H4 : MatchSubst (a_CApp a g_Triv) p1 b1 a2)
  (H5 : SubRole R0 R1),
  Value R1 a.
Proof.
  intros.
  move: (MatchSubst_match H4) => h4.
  eapply Value_Path with (F:=F).
  eapply CasePath_UnMatch; eauto.
  + inversion h4; subst. eapply tm_pattern_agree_ValuePath; eauto.
    eapply tm_subpattern_agree_sub_capp. econstructor.
    eapply Rename_tm_pattern_agree; eauto.
  + move: (tm_pattern_agree_rename_inv_2 h4 H3) => h5. 
    intro. eapply subtm_pattern_agree_capp_contr; eauto.
Qed.


Lemma AppsPath_Value : forall F Apps a R, AppsPath R a F Apps -> Value R a.
Proof.
  intros.
  eapply Value_Path.
  eauto using AppsPath_CasePath.
Admitted.

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
(*  all: try solve [(have: False; try done; inversion H; inversion H1)]. *)
(*  all: try solve [(have: False; try done; inversion H0; inversion H1)]. *)
  all: try solve [invert_MatchSubst].
  (* AbsTerm *)
  - autofresh. hide Fr.
    match goal with 
      [ H0 : forall a2 : tm, (reduction_in_one ?a a2 ?R) -> _ , 
        H2 : reduction_in_one ?a _ _ |- _ ] => 
      move: (H0 _ H2) => h7 end.
    apply open_tm_wrt_tm_inj in h7; eauto. rewrite h7. auto.
  - (* left side is AppLeft, right side is Beta_Axiom *)
    (* Need to show that if Beta_Axiom triggers, then the 
       term is a Value. *)
    have VF: Value R1 a. eapply BetaAxiom_a_App_only; eauto.
    Value_no_red.
  - inversion H; inversion H1; invert_MatchSubst.
  - (* left side is Beta_Axiom, right side is CApp. *)
    have VF: Value R a. eapply BetaAxiom_a_CApp_only; eauto.
    Value_no_red.
  - (* left side is scrutinee evaluation, right is Beta *)
    inversion H2. invert_MatchSubst.
    have VF: Value Nom a. eauto using AppsPath_Value.
    Value_no_red.
    Value_no_red.
  - (* left size is Beta_Axiom, right side is AppLeft. *)
    have VF: Value R a0. eapply BetaAxiom_a_App_only; eauto.
    Value_no_red.
  - inversion H0; inversion H1; invert_MatchSubst.
  - (* left side is CApp. right side is Beta_Axiom *)
    have VF: Value R a0. eapply BetaAxiom_a_CApp_only; eauto.
    Value_no_red.
  - (* left side is Beta, right side is scrutinee eval *)
    inversion H. invert_MatchSubst.
    have VF: Value Nom a0. eauto using AppsPath_Value.
    Value_no_red.
    Value_no_red.
Qed.
