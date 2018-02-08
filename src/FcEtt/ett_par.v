Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Import FcEtt.utils.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.


Require Export FcEtt.ext_context_fv.

Require Import FcEtt.ext_wf.
Require Import FcEtt.ett_erased.
Import ext_wf.



(* Require Import FcEtt.erase_syntax. *)

Require Export FcEtt.toplevel.

Require Export FcEtt.ett_value.


Lemma par_app_rctx : forall W1 W2 W3 a a' R, uniq (W1 ++ W2 ++ W3) ->
                     Par (W1 ++ W3) a a' R -> 
                     Par (W1 ++ W2 ++ W3) a a' R.
Proof. intros W1 W2 W3 a a' R U H. generalize dependent W2.
       dependent induction H; intros; eauto.
        - econstructor. eapply erased_app_rctx; eauto.
        - eapply Par_Abs with (L := union L (dom (W1 ++ W2 ++ W3))).
          intros. rewrite <- app_assoc.
          eapply H0; eauto. simpl_env. auto.
        - eapply Par_Pi with (L := union L (dom (W1 ++ W2 ++ W3))); eauto.
          intros. rewrite <- app_assoc.
          eapply H1; eauto. simpl_env. auto.
        - econstructor; eauto.
        - econstructor. eapply erased_app_rctx; eauto.
Qed.

(* ------------------------------------------ *)

(* Synatactic properties about parallel reduction. (Excluding confluence.) *)

(* ------------------------------------------ *)


(* TODO: move these definitions to the OTT file. *)

Inductive multipar W ( a : tm) : tm -> role -> Prop :=
| mp_refl : forall R, erased_tm W a R -> multipar W a a R
| mp_step : forall R b c, Par W a b R -> multipar W b c R -> 
                                             multipar W a c R.

Hint Constructors multipar.

Lemma multipar_app_rctx : forall W1 W2 W3 a a' R, uniq (W1 ++ W2 ++ W3) ->
                     multipar (W1 ++ W3) a a' R -> 
                     multipar (W1 ++ W2 ++ W3) a a' R.
Proof. intros W1 W2 W3 a a' R U H. generalize dependent W2.
       dependent induction H; intros; eauto.
        - econstructor. eapply erased_app_rctx; eauto.
        - econstructor; eauto. apply par_app_rctx; auto.
Qed.

Definition joins W a b R := exists c, multipar W a c R /\ multipar W b c R.

Lemma Par_lc1 : forall W a a' R , Par W a a' R -> lc_tm a.
  intros.  induction H; auto; eapply erased_lc; eauto.
Qed.

(* FIXME: find a good place for this tactic. *)
(* cannot move this to ett_ind.v because need Toplevel_lc ??? *)
Ltac lc_toplevel_inversion :=
  match goal with
  | [ b : binds ?F _ toplevel |- _ ] =>
    apply Toplevel_lc in b; inversion b; auto
end.

Lemma Par_lc2 : forall W a a' R, Par W a a' R -> lc_tm a'.
Proof.
  intros. induction H; auto.
  - lc_solve.
  - lc_solve.
  - lc_solve.
  - lc_toplevel_inversion.
  - inversion IHPar1. constructor; auto.
  - inversion IHPar1. constructor; auto.
  - inversion IHPar. constructor; auto.
Qed.

Hint Resolve Par_lc1 Par_lc2 : lc.

Lemma Par_erased_tm_fst : forall W a a' R, Par W a a' R -> 
                                               erased_tm W a R.
Proof. intros W a a' R H. induction H; eauto.
Qed.

Lemma multipar_erased_tm_fst: forall W a a' R, multipar W a a' R -> 
                                               erased_tm W a R.
Proof. intros. induction H. auto. eapply Par_erased_tm_fst; eauto.
Qed.

Lemma Par_erased_tm_snd : forall W a a' R, Par W a a' R ->
                                               erased_tm W a' R.
Proof. intros W a a' R H. induction H; eauto.
        - inversion IHPar1; subst. pick fresh x.
          erewrite tm_subst_tm_tm_intro; eauto.
          replace W with (nil ++ W); auto. eapply subst_tm_erased; eauto.
        - inversion IHPar; subst. pick fresh c.
          erewrite co_subst_co_tm_intro; eauto.
          replace W with (nil ++ W); auto. eapply subst_co_erased; eauto.
        - eapply erased_sub. eapply toplevel_erased1; eauto. auto.
        - inversion IHPar1; eauto.
        - inversion IHPar1; eauto.
        - inversion IHPar; eauto.
        - econstructor. admit.
Admitted.

Lemma multipar_erased_tm_snd : forall W a a' R, multipar W a a' R ->
                                               erased_tm W a' R.
Proof. intros. induction H; auto.
Qed.

Lemma Par_rctx_uniq : forall W a a' R, Par W a a' R -> uniq W.
Proof. intros. eapply rctx_uniq. eapply Par_erased_tm_fst; eauto.
Qed.

Lemma multipar_rctx_uniq: forall W a a' R, multipar W a a' R -> uniq W.
Proof. intros. eapply rctx_uniq. eapply multipar_erased_tm_fst; eauto.
Qed.

Lemma par_multipar: forall W a a' R, Par W a a' R -> 
                                         multipar W a a' R.
Proof. intros. eapply mp_step. eauto. constructor. 
       eapply Par_erased_tm_snd; eauto.
Qed. 

Hint Resolve Par_erased_tm_fst Par_erased_tm_snd : erased.

(* ------------------------------------------------------------- *)

Lemma Par_sub: forall W a a' R1 R2, Par W a a' R1 -> SubRole R1 R2 ->
                                      Par W a a' R2.
Proof. intros W a a' R1 R2 H SR. generalize dependent R2.
       induction H; intros; simpl; eauto. econstructor.
       eapply erased_sub; eauto.
Qed.

Lemma multipar_sub : forall W a a' R1 R2, multipar W a a' R1 ->
                     SubRole R1 R2 -> multipar W a a' R2.
Proof. intros. induction H. econstructor. eapply erased_sub; eauto.
       econstructor; eauto. eapply Par_sub; eauto.
Qed.

Lemma subst1 : forall b W W' a a' R1 R2 x, Par W' a a' R1 -> 
               erased_tm (W ++ [(x,R1)] ++ W') b R2 ->
               Par (W ++ W') (tm_subst_tm_tm a x b) (tm_subst_tm_tm a' x b) R2.
Proof.
  intros b W W' a a' R1 R2 x PAR ET.
  dependent induction ET; intros; simpl; auto.
   - constructor. constructor. eapply uniq_remove_mid; eauto.
   - constructor. constructor. eapply uniq_remove_mid; eauto.
   - destruct (x0 == x); auto. 
     + subst. assert (P:R = R1).
       eapply binds_mid_eq; eauto. subst. replace W with (nil ++ W); eauto.
       rewrite app_assoc. eapply par_app_rctx.
       simpl_env. eapply uniq_remove_mid; eauto.
       simpl_env; eauto. eapply Par_sub; eauto.
     + econstructor. econstructor. eapply uniq_remove_mid; eauto.
       eapply binds_remove_mid; eauto. auto.
   - eapply Par_Abs with (L := union (singleton x) L).
     intros x0 H1.
     rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1.
     rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1.
     rewrite <- app_assoc. eapply H0; eauto.
     eapply Par_lc2; eauto. eapply Par_lc1; eauto.
   - econstructor; eauto.
   - eapply Par_Pi with (L := union (singleton x) L); eauto.
     intros x0 H1.
     rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1.
     rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1.
     rewrite <- app_assoc. eapply H0; eauto.
     eapply Par_lc2; eauto. eapply Par_lc1; eauto.
   - eapply Par_CPi with (L := union L (singleton x)); eauto.
     intros c H1.
     rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1.
     rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1. eapply H0; eauto.
     eapply Par_lc2; eauto. eapply Par_lc1; eauto.
   - eapply Par_CAbs with (L := union L (singleton x)); eauto.
     intros c H1.
     rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1.
     rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1. eapply H0; eauto.
     eapply Par_lc2; eauto. eapply Par_lc1; eauto.
   - econstructor; eauto.
   - econstructor; eauto.
   - econstructor; eauto.
Qed.

Lemma open1 : forall b W L a a' R, Par W a a' R
  -> (forall x, x `notin` L -> erased_tm W (open_tm_wrt_tm b (a_Var_f x)) R)
  -> Par W (open_tm_wrt_tm b a) (open_tm_wrt_tm b a') R.
Proof.
  intros.
  pick fresh x.
  rewrite (tm_subst_tm_tm_intro x); auto.
  rewrite [(_ _ a')] (tm_subst_tm_tm_intro x); auto.
  replace W with (nil ++ W); auto. eapply subst1; eauto.
  apply erased_app_rctx; simpl_env.
  constructor; auto. eapply Par_rctx_uniq; eauto.
  auto.
Qed.


Lemma subst2 : forall b W W' a a' R R1 x, 
          Par (W ++ [(x,R1)] ++ W') a a' R -> 
          erased_tm W' b R1 ->
          Par (W ++ W') (tm_subst_tm_tm b x a) (tm_subst_tm_tm b x a') R.
Proof.
  intros b W W' a a' R R1 x PAR E.
  dependent induction PAR; simpl. 
  all: eauto using tm_subst_tm_tm_lc_tm.
  all: autorewrite with subst_open; eauto.
  all: try eapply erased_lc; eauto.
  - econstructor. eapply subst_tm_erased; eauto.
  - eapply Par_Abs with (L := union L (singleton x)).
    intros x0 H1.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1.
    rewrite <- app_assoc. eapply H0. auto. simpl_env; auto.
    auto. eapply erased_lc; eauto. eapply erased_lc; eauto.
  - eapply Par_Pi with (L := union L (singleton x)); eauto.
    intros x0 H2.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1.
    rewrite <- app_assoc. eapply H0. auto. simpl_env; auto.
    auto. eapply erased_lc; eauto. eapply erased_lc; eauto.
  - eapply Par_CAbs with (L := union L (singleton x)).
    intros x0 H1.
    rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1.
    rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1.
    eapply H0. auto. eauto. auto.
    eapply erased_lc; eauto. eapply erased_lc; eauto.
  - eapply Par_CPi with (L := union L (singleton x)); eauto.
    intros x0 H4.
    rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1.
    rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1.
    eapply H0. auto. eauto. auto.
    eapply erased_lc; eauto. eapply erased_lc; eauto.
  - eapply Par_Axiom; eauto. 
    rewrite tm_subst_tm_tm_fresh_eq. eauto.
    apply toplevel_closed in H.
    apply Typing_context_fv in H.
    split_hyp. simpl in *.
    fsetdec.
  - pose (P := IHPAR _ _ _ _ ltac:(auto) E). simpl in P. auto.
  - econstructor; eauto 2. pose (P := IHPAR1 _ _ _ _ ltac:(auto) E).
    simpl in P. auto.
  - eapply Par_PushCombine; eauto 2. pose (P := IHPAR1 _ _ _ _ ltac:(auto) E).
    simpl in P. auto. pose (P := IHPAR2 _ _ _ _ ltac:(auto) E).
    simpl in P. auto.
  - econstructor; eauto. pose (P := IHPAR _ _ _ _ ltac:(auto) E).
    simpl in P. auto.
Qed.


Lemma subst3 : forall b b' W W' a a' R R1 x, 
          Par (W ++ [(x,R1)] ++ W') a a' R -> 
          Par W' b b' R1 ->
          Par (W ++ W') (tm_subst_tm_tm b x a) (tm_subst_tm_tm b' x a') R.
Proof.
  intros.
  dependent induction H; simpl; eauto 2; erased_inversion; eauto 4.
  all: try solve [ Par_pick_fresh y;
              autorewrite with subst_open_var; eauto 3 with lc ].
  all: try solve [ autorewrite with subst_open; eauto 4 with lc ].
  - eapply subst1; eauto.
  - eapply Par_Abs with (L := union L (singleton x)).
    intros x0 H2.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1.
    rewrite <- app_assoc. eapply H0. auto. simpl_env; auto.
    auto. eapply Par_lc2; eauto. eapply Par_lc1; eauto.
  - eapply Par_Pi with (L := union (singleton x) L); eauto.
    intros x0 H3.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1.
    rewrite <- app_assoc. eapply H1; eauto. simpl_env; auto.
    eapply Par_lc2; eauto. eapply Par_lc1; eauto.
  - eapply Par_Axiom; eauto.
    rewrite tm_subst_tm_tm_fresh_eq. eauto.
    apply toplevel_closed in H.
    apply Typing_context_fv in H.
    split_hyp. simpl in *.
    fsetdec.
  - pose (P := IHPar _ _ _ _ ltac:(auto) H0). simpl in P. auto.
  - econstructor; eauto 2. pose (P := IHPar1 _ _ _ _ ltac:(auto) H1).
    simpl in P. auto.
  - eapply Par_PushCombine; eauto 2. pose (P := IHPar1 _ _ _ _ ltac:(auto) H1).
    simpl in P. auto. pose (P := IHPar2 _ _ _ _ ltac:(auto) H1).
    simpl in P. auto.
  - econstructor; eauto. pose (P := IHPar _ _ _ _ ltac:(auto) H0).
    simpl in P. auto.
Qed.

Lemma subst4 : forall b x, lc_co b ->
    forall W a a' R, Par W a a' R ->
    Par W (co_subst_co_tm b x a) (co_subst_co_tm b x a') R.
Proof.
  intros b x EB W a a' R PAR.
  induction PAR; simpl; auto.
  all: try solve [ Par_pick_fresh y;
              autorewrite with subst_open_var; eauto 3 with lc ].
  all: try solve [ autorewrite with subst_open; eauto 4 with lc ].
  - apply Par_Refl. eapply subst_co_erased; eauto.
  - rewrite co_subst_co_tm_fresh_eq. eauto.
    apply toplevel_closed in H.
    apply Typing_context_fv in H.
    split_hyp. simpl in *.
    fsetdec.
Qed.

Lemma multipar_subst3 : forall b b' W W' a a' R R1 x, 
     multipar (W ++ [(x,R1)] ++ W') a a' R -> 
     multipar W' b b' R1 ->
     multipar (W ++ W') (tm_subst_tm_tm b x a) (tm_subst_tm_tm b' x a') R.
Proof.
  intros b b' W W' a a' R R1 x H1 H2.
  dependent induction H1; auto.
  - dependent induction H2; auto.
    constructor. eapply subst_tm_erased; eauto.
    apply (@mp_step _ _ _ ((tm_subst_tm_tm b x a))); auto.
    eapply subst3; eauto.
  - dependent induction H2; auto.
    apply (@mp_step _ _ _ (tm_subst_tm_tm a0 x b0)); auto.
    eapply subst3; eauto.
    apply (@mp_step _ _ _ ((tm_subst_tm_tm a0 x b0))); auto.
    eapply subst2; eauto. eapply Par_erased_tm_fst; eauto.
    apply IHmultipar; auto.
    econstructor; eauto.
Qed.

Lemma multipar_subst4 : forall W b x, lc_co b ->
    forall a a' R, multipar W a a' R ->
    multipar W (co_subst_co_tm b x a) (co_subst_co_tm b x a') R.
Proof.
  intros W b x H a a' R H0.
  dependent induction H0; eauto.
  constructor. eapply subst_co_erased; eauto.
  apply (@mp_step _ _ _ (co_subst_co_tm b x b0)); auto.
  apply subst4; auto.
Qed.

Lemma erased_tm_open_tm_wrt_tm: forall W a R x, erased_tm W a R -> erased_tm W (open_tm_wrt_tm a (a_Var_f x)) R.
Proof.
  intros W a R x H.
  pose K := erased_lc H.
  rewrite open_tm_wrt_tm_lc_tm; eauto.
Qed.

Hint Resolve erased_tm_open_tm_wrt_tm : erased.


Lemma Par_Pi_exists: ∀ x W rho (A B A' B' : tm) R R',
    x `notin` fv_tm_tm_tm B -> Par W A A' R
    → Par ([(x,R)] ++ W) (open_tm_wrt_tm B (a_Var_f x)) B' R'
    → Par W (a_Pi rho A R B) (a_Pi rho A' R (close_tm_wrt_tm x B')) R'.
Proof.
  intros x W rho A B A' B' R R' H H0 H1.
  apply (Par_Pi (union (singleton x) (union (dom W) (fv_tm_tm_tm B)))); eauto.
  intros x0 h0.
  rewrite -tm_subst_tm_tm_spec.
  rewrite (tm_subst_tm_tm_intro x B (a_Var_f x0)); auto.
  replace ([(x0,R)] ++ W) with (nil ++ [(x0,R)] ++ W); auto.
  assert (uniq ([(x,R)] ++ W)). {eapply Par_rctx_uniq; eauto. }
  eapply subst2; eauto.
  simpl_env. apply par_app_rctx; eauto 1. solve_uniq.
  econstructor. solve_uniq. auto. auto.
Qed.

Lemma Par_CPi_exists:  ∀ c W (A B a A' B' a' T T': tm) R R',
       c `notin` fv_co_co_tm a -> Par W A A' R
       → Par W B B' R -> Par W T T' R
         → Par W (open_tm_wrt_co a (g_Var_f c)) (a') R'
         → Par W (a_CPi (Eq A B T R) a) (a_CPi (Eq A' B' T' R) (close_tm_wrt_co c a')) R'.
Proof.
  intros c W A B a A' B' a' T T' R R' H H0 H1 h0 H2.
  apply (Par_CPi (singleton c)); auto.
  intros c0 H3.
  rewrite -co_subst_co_tm_spec.
  rewrite (co_subst_co_tm_intro c  a (g_Var_f c0));  auto.
  apply subst4; auto.
Qed.


Lemma Par_Abs_exists: ∀ x W rho R R' (a a' : tm),
    x `notin` fv_tm_tm_tm a
    → Par ([(x,R)] ++ W) (open_tm_wrt_tm a (a_Var_f x)) a' R'
    → Par W (a_UAbs rho R a) (a_UAbs rho R (close_tm_wrt_tm x a')) R'.
Proof.
  intros x W rho R R' a a' hi0 H0.
  apply (Par_Abs (union (singleton x) (dom W))); eauto.
  intros x0 h0.
  rewrite -tm_subst_tm_tm_spec.
  rewrite (tm_subst_tm_tm_intro x a (a_Var_f x0)); auto.
  replace ([(x0,R)] ++ W) with (nil ++ [(x0,R)] ++ W); auto.
  assert (uniq ([(x,R)] ++ W)). {eapply Par_rctx_uniq; eauto. }
  eapply subst2; eauto.
  simpl_env. apply par_app_rctx; eauto 1.
  solve_uniq. econstructor. solve_uniq. auto. auto.
Qed.

Lemma Par_CAbs_exists: forall c W (a a': tm) R,
       c `notin` fv_co_co_tm a
       -> Par W (open_tm_wrt_co a (g_Var_f c)) a' R
       → Par W (a_UCAbs a) (a_UCAbs (close_tm_wrt_co c a')) R.
Proof.
  intros c W a a' R H H0.
  apply (Par_CAbs (singleton c)); auto.
  intros c0 H3.
  rewrite -co_subst_co_tm_spec.
  rewrite (co_subst_co_tm_intro c  a (g_Var_f c0));  auto.
  apply subst4; auto.
Qed.

Lemma Par_open_tm_wrt_co_preservation: forall W B1 B2 c R, 
  Par W (open_tm_wrt_co B1 (g_Var_f c)) B2 R ->
  exists B', B2 = open_tm_wrt_co B' (g_Var_f c)
    /\ Par W (open_tm_wrt_co B1 (g_Var_f c)) (open_tm_wrt_co B' (g_Var_f c)) R.
Proof.
  intros W B1 B2 c R H.
  exists (close_tm_wrt_co c B2).
  have:open_tm_wrt_co (close_tm_wrt_co c B2) (g_Var_f c) = B2 by apply open_tm_wrt_co_close_tm_wrt_co.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.

Lemma Par_open_tm_wrt_tm_preservation: forall W B1 B2 x R,
  Par W (open_tm_wrt_tm B1 (a_Var_f x)) B2 R ->
  exists B', B2 = open_tm_wrt_tm B' (a_Var_f x)
    /\ Par W (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)) R.
Proof.
  intros W B1 B2 x R H.
  exists (close_tm_wrt_tm x B2).
  have:open_tm_wrt_tm (close_tm_wrt_tm x B2) (a_Var_f x) = B2 by apply open_tm_wrt_tm_close_tm_wrt_tm.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.

Lemma multipar_Pi_exists: ∀ x W rho (A B A' B' : tm) R R',
       x `notin` fv_tm_tm_tm B ->
       multipar W A A' R
       → multipar ([(x,R)] ++ W) (open_tm_wrt_tm B (a_Var_f x)) B' R'
       → multipar W (a_Pi rho A R B) (a_Pi rho A' R (close_tm_wrt_tm x B')) R'.
Proof.
  intros x W rho A B A' B' R R' e H H0.
  dependent induction H; eauto.
  - dependent induction H0; eauto.
    erewrite close_tm_wrt_tm_open_tm_wrt_tm; eauto.
    constructor. eapply erased_Pi_some_any; eauto.
    apply (@mp_step _ _ _ (a_Pi rho a R (close_tm_wrt_tm x b))); auto.
    + eapply Par_Pi_exists; eauto.
    + apply IHmultipar; auto.
      * rewrite fv_tm_tm_tm_close_tm_wrt_tm_rec.
        fsetdec.
      * rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.
  - apply (@mp_step _ _ _ (a_Pi rho b R B)); auto.
    apply (Par_Pi (union (singleton x) (union (dom W) (fv_tm_tm_tm B)))). 
    auto. intros. econstructor. 
    assert (uniq ([(x,R)] ++ W)). {eapply multipar_rctx_uniq; eauto. }
    rewrite (tm_subst_tm_tm_intro x B (a_Var_f x0)); auto.
    replace ([(x0,R)] ++ W) with (nil ++ [(x0,R)] ++ W); auto.
    eapply subst_tm_erased. simpl_env. apply erased_app_rctx.
    solve_uniq. eapply multipar_erased_tm_fst; eauto.
    econstructor. solve_uniq. auto. auto.
Qed.


Lemma multipar_Pi_A_proj: ∀ W rho (A B A' B' : tm) R R',
    multipar W (a_Pi rho A R B) (a_Pi rho A' R B') R' ->
    multipar W A A' R.
Proof.
  intros W rho A B A' B' R R' h1.
  dependent induction h1.
  - inversion H. constructor. auto.
  - inversion H. subst. eapply IHh1; eauto.
    apply mp_step with (b := A'0). auto.
    eapply IHh1; eauto.
Qed.

Lemma multipar_Pi_B_proj: ∀ W rho (A B A' B' : tm) R R',
    multipar W (a_Pi rho A R B) (a_Pi rho A' R B') R' →
    exists L, forall x, x `notin` L -> 
      multipar ([(x,R)] ++ W) (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)) R'.
Proof.
  intros W rho A B A' B' R R' h1.
  dependent induction h1; eauto.
  - inversion H. subst. exists L. intros.
    constructor. auto.
  - inversion H; subst.
    eapply IHh1; eauto.
    destruct (IHh1 rho A'0 B'0 A' B' R) as [L0 h0]; auto.
    exists (L \u L0); eauto.
Qed.


Lemma multipar_CPi_exists:  ∀ c W (A B a T A' B' a' T': tm) R R',
       c `notin` fv_co_co_tm a ->
       multipar W A A' R →
       multipar W B B' R ->
       multipar W T T' R →
       multipar W (open_tm_wrt_co a (g_Var_f c)) a' R' →
       multipar W (a_CPi (Eq A B T R) a) (a_CPi (Eq A' B' T' R) (close_tm_wrt_co c a')) R'.
Proof.
  intros c W A B a T A' B' a' T' R R' e H H0 H2 H1.
  dependent induction H; eauto 1.
  - dependent induction H0; eauto 1.
    + dependent induction H1; eauto 1.
      * dependent induction H2; eauto 1.
        rewrite close_tm_wrt_co_open_tm_wrt_co; auto.
        constructor. econstructor; eauto 1.
        intros. rewrite (co_subst_co_tm_intro c).
        apply subst_co_erased. auto. auto. auto.
        apply mp_step with (b:= (a_CPi (Eq a0 a1 b R) a)); eauto.
        econstructor; eauto 2. intros. constructor.
        rewrite (co_subst_co_tm_intro c).
        apply subst_co_erased. auto. auto. auto.
      * eapply mp_step with (b:= (a_CPi (Eq a0 a1 T R) (close_tm_wrt_co c b))); eauto.
        -- apply Par_CPi_exists; auto 2. constructor.
           eapply multipar_erased_tm_fst; eauto.
        -- apply IHmultipar; eauto.
           ++ rewrite fv_co_co_tm_close_tm_wrt_co_rec.
              fsetdec.
           ++ rewrite open_tm_wrt_co_close_tm_wrt_co; auto.
      + eapply mp_step with (b:= (a_CPi (Eq a0 b T R) a)); eauto.
        -- apply (Par_CPi (singleton c)); auto 2.
           constructor. eapply multipar_erased_tm_fst; eauto.
           intros. constructor. rewrite (co_subst_co_tm_intro c).
           apply subst_co_erased. auto. eapply multipar_erased_tm_fst; eauto.
           auto.
  - apply mp_step with (b:= (a_CPi (Eq b B T R) a)); auto.
     apply (Par_CPi (singleton c)); auto.
     constructor. eapply multipar_erased_tm_fst; eauto.
     constructor. eapply multipar_erased_tm_fst; eauto.
     intros. constructor. rewrite (co_subst_co_tm_intro c).
     apply subst_co_erased. auto. eapply multipar_erased_tm_fst; eauto.
     auto. Unshelve. apply (fv_co_co_tm a). apply (fv_co_co_tm a).
Qed.


Lemma multipar_CPi_B_proj:  ∀ W (A B a A' B' a' T T': tm) R1 R2 R',
    multipar W (a_CPi (Eq A B T R1) a) (a_CPi (Eq A' B' T' R2) a') R' →
    exists L, forall c, c `notin` L ->
      multipar W (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co a' (g_Var_f c)) R'.
Proof.
  intros W A B a A' B' a' T T' R1 R2 R' h1.
  dependent induction h1; eauto.
  - inversion H. subst. exists L. intros.
    constructor. auto.
  - inversion H; subst.
    eapply IHh1; eauto.
    destruct (IHh1 _ _ _ _ _ _ _ _ _ _ ltac:(auto) ltac:(auto)) as [L0 h0]; auto.
    exists (L \u L0); eauto.
Qed.

Lemma multipar_CPi_phi_proj:  ∀ W (A B a A' B' a' T T': tm) R R',
    multipar W (a_CPi (Eq A B T R) a) (a_CPi (Eq A' B' T' R) a') R' ->
    multipar W A A' R 
      /\ multipar W B B' R
      /\ multipar W T T' R.
Proof.
  intros W A B a A' B' a' T T' R R' H.
  dependent induction H; eauto.
  - inversion H; subst. split. constructor; auto.
    split. all:constructor; auto.
  - inversion H; subst.
    eapply IHmultipar; eauto.
    destruct (IHmultipar _ _ _ _ _ _ _ _ _ ltac:(auto) ltac:(auto))
    as [H1 [H2 H3]].
    repeat split.
    apply mp_step with (b := a'0); auto.
    apply mp_step with (b := b'); auto.
    apply mp_step with (b := A'0); auto.
Qed.


Lemma multipar_Abs_exists: ∀ x W rho R R' (a a' : tm),
       x `notin` fv_tm_tm_tm a →
       multipar ([(x,R)] ++ W) (open_tm_wrt_tm a (a_Var_f x)) a' R' →
       multipar W (a_UAbs rho R a) (a_UAbs rho R (close_tm_wrt_tm x a')) R'.
Proof.
  intros x W rho R R' B B' e H.
  dependent induction H; eauto 2.
  - autorewrite with lngen. constructor.
    assert (uniq ([(x,R)] ++ W)). {eapply rctx_uniq; eauto. }
    apply erased_a_Abs with (L := union (singleton x) (dom W)).
    intros. rewrite (tm_subst_tm_tm_intro x B (a_Var_f x0)); auto.
    replace ([(x0,R)] ++ W) with (nil ++ [(x0,R)] ++ W); auto.
    apply subst_tm_erased with (R1 := R). simpl_env. apply erased_app_rctx.
    solve_uniq. auto. econstructor; auto. solve_uniq.
  - assert (Par W (a_UAbs rho R B) (a_UAbs rho R (close_tm_wrt_tm x b)) R0).
    eapply (Par_Abs_exists); auto.
    assert (multipar W (a_UAbs rho R (close_tm_wrt_tm x b))
                       (a_UAbs rho R (close_tm_wrt_tm x c)) R0).
    { apply IHmultipar; auto.
    * rewrite fv_tm_tm_tm_close_tm_wrt_tm_rec.
      fsetdec.
    * rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto. }
    eapply mp_step; eauto.
Qed.

Lemma multipar_CAbs_exists: forall c W (a a': tm) R,
       c `notin` fv_co_co_tm a →
       multipar W (open_tm_wrt_co a (g_Var_f c)) a' R →
       multipar W (a_UCAbs a) (a_UCAbs (close_tm_wrt_co c a')) R.
Proof.
  intros c W a a' R e H.
  dependent induction H; eauto 1.
  - rewrite close_tm_wrt_co_open_tm_wrt_co; auto.
    econstructor. apply erased_a_CAbs with (L := fv_co_co_tm a).
    intros. rewrite (co_subst_co_tm_intro c); auto.
    apply subst_co_erased. auto. auto.
  - apply mp_step with (b := ((a_UCAbs (close_tm_wrt_co c b)))); eauto.
    apply Par_CAbs_exists; auto.
    apply IHmultipar; eauto.
    rewrite fv_co_co_tm_close_tm_wrt_co_rec. fsetdec.
    rewrite open_tm_wrt_co_close_tm_wrt_co; auto.
Qed.

Lemma multipar_open_tm_wrt_co_preservation: forall W B1 B2 c R,
  multipar W (open_tm_wrt_co B1 (g_Var_f c)) B2 R ->
  exists B', B2 = open_tm_wrt_co B' (g_Var_f c)
    /\ multipar W (open_tm_wrt_co B1 (g_Var_f c)) (open_tm_wrt_co B' (g_Var_f c)) R.
Proof.
  intros W B1 B2 c R H.
  exists (close_tm_wrt_co c B2).
  have:open_tm_wrt_co (close_tm_wrt_co c B2) (g_Var_f c) = B2 by apply open_tm_wrt_co_close_tm_wrt_co.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.

Lemma multipar_open_tm_wrt_tm_preservation: forall W B1 B2 R x,
  multipar W (open_tm_wrt_tm B1 (a_Var_f x)) B2 R ->
  exists B', B2 = open_tm_wrt_tm B' (a_Var_f x)
    /\ multipar W (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)) R.
Proof.
  intros W B1 B2 R x H.
  exists (close_tm_wrt_tm x B2).
  have:open_tm_wrt_tm (close_tm_wrt_tm x B2) (a_Var_f x) = B2 by apply open_tm_wrt_tm_close_tm_wrt_tm.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.

Lemma multipar_Cast_exists : forall W a1 a2 R R', multipar W a1 a2 R ->
               multipar W (a_Conv a1 R' g_Triv) (a_Conv a2 R' g_Triv) R.
Proof. intros. induction H. econstructor. econstructor. auto.
       econstructor. eapply Par_Cong; eauto. auto.
Qed.