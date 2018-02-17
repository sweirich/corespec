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
Import ext_wf.



(* Require Import FcEtt.erase_syntax. *)

Require Export FcEtt.toplevel.

Require Export FcEtt.ett_value.


Lemma rctx_uniq : forall W a R, erased_tm W a R -> uniq W.
Proof. intros W a R H. induction H; eauto.
        - pick fresh x. eapply uniq_app_2; eauto.
        - pick fresh c; eauto.
Qed.

Lemma erased_app_rctx : forall W1 W2 W3 a R, uniq (W1 ++ W2 ++ W3) -> 
                               erased_tm (W1 ++ W3) a R ->
                               erased_tm (W1 ++ W2 ++ W3) a R.
Proof. intros W1 W2 W3 a R U H. generalize dependent W2. 
       dependent induction H; intros; eauto.
        - eapply erased_a_Abs with (L := union L (dom (W1 ++ W2 ++ W3))).
          intros. rewrite <- app_assoc.
          eapply H0; eauto. simpl_env. auto.
        - eapply erased_a_Pi with (L := union L (dom (W1 ++ W2 ++ W3))); eauto.
          intros. rewrite <- app_assoc.
          eapply H1; eauto. simpl_env. auto.
        - econstructor; eauto.
Qed.

(* NOTE: we have a database 'erased' for proving that terms are erased. *)

(* Tactics concerning erased terms. *)

Ltac erased_pick_fresh x :=
  match goal with
    [ |- erased_tm ?s ?R ] =>
    let v := match s with
             | a_UAbs _ _ _ => erased_a_Abs
             | a_Pi _ _ _ _ => erased_a_Pi
             | a_CPi _ _   => erased_a_CPi
             | a_UCAbs _   => erased_a_CAbs
             end
    in pick fresh x and apply v
  end.

Ltac erased_inversion :=
  repeat match goal with
  | [H : erased_tm (a_UAbs _ _ _) _ |- _ ] =>
    inversion H; subst; clear H
  | [H : erased_tm (a_App _ _ _ _) _ |- _ ] =>
    inversion H; subst; clear H
  | [H : erased_tm (a_Pi _ _ _ _) _ |- _ ] =>
    inversion H; subst; clear H
  | [H : erased_tm (a_CPi _ _) _ |- _ ] =>
    inversion H; subst; clear H
  | [H : erased_tm (a_UCAbs _ ) _ |- _ ] =>
    inversion H; subst; clear H
  | [H : erased_tm (a_CApp _ _) _ |- _ ] =>
    inversion H; subst; clear H
end.


Inductive erased_sort (W : role_context) : sort -> Prop := 
| erased_Tm : forall a R, erased_tm W a R -> erased_sort W (Tm a R)
| erased_Co : forall a b A R, erased_tm W a R -> erased_tm W b R -> erased_tm W A R -> erased_sort W (Co (Eq a b A R)).

(* Check Forall_forall FIXME:?? *)


Inductive erased_context : role_context -> context -> Prop :=
 | nil_erased_ctx : erased_context nil nil
 | co_erased_ctx : forall W G c a b A R,
                   erased_sort W (Co (Eq a b A R)) -> erased_context W G -> 
                   erased_context W ([(c, (Co (Eq a b A R)))] ++ G)
 | tm_erased_ctx : forall W G x A R, erased_context W G ->
                   erased_sort W (Tm A R) ->
                   erased_context ([(x,R)] ++ W) ([(x, (Tm A R))] ++ G).

Lemma dom_rctx_le_ctx : forall G, dom (ctx_to_rctx G) [<=] dom G.
Proof. intros. induction G. auto. destruct a, s; simpl; fsetdec.
Qed.

Lemma notin_ctx_rctx : forall x G, x `notin` (dom G) -> x `notin` dom (ctx_to_rctx G).
Proof. intros. induction G. auto. destruct a, s; simpl in *.
       all : pose (P := H); apply notin_add_2 in P; fsetdec.
Qed.

Lemma dom_erased_ctx_rctx_le_ctx : forall W G, erased_context W G ->
                                               dom W [<=] dom G.
Proof. intros; induction H; simpl; fsetdec.
Qed.

Lemma uniq_erased_ctx_rctx : forall W G, erased_context W G -> uniq G
                                          -> uniq W.
Proof. intros. induction H; auto.
       apply IHerased_context. eapply uniq_app_2; eauto.
       inversion H0. apply IHerased_context in H4. constructor.
       auto. apply dom_erased_ctx_rctx_le_ctx in H. fsetdec.
Qed.

Lemma erased_lc : forall W a R, erased_tm W a R -> lc_tm a.
intros; induction H; auto.
Qed.

Hint Resolve erased_lc : lc.

Lemma erased_sub : forall W a R1 R2, erased_tm W a R1 -> SubRole R1 R2 ->
                                     erased_tm W a R2.
Proof. intros W a R1 R2 H S. induction H; eauto.
       econstructor; eauto.
Qed.

Lemma subst_tm_erased : forall W1 x R1 W2 a R b, 
               erased_tm (W1 ++ [(x,R1)] ++ W2) a R ->
               erased_tm W2 b R1 -> 
               erased_tm (W1 ++ W2) (tm_subst_tm_tm b x a) R.
Proof.
  intros W1 x R1 W2 a R b H1 H2. dependent induction H1; simpl; eauto.
  - destruct (x0 == x); auto. 
     + subst. assert (P:R = R1).
       eapply binds_mid_eq; eauto. subst. replace W1 with (nil ++ W1); eauto.
       rewrite app_assoc. eapply erased_app_rctx; simpl_env; eauto.
       eapply erased_sub; eauto.
     + econstructor. eapply uniq_remove_mid; eauto.
       eapply binds_remove_mid; eauto. eauto.
  - pick fresh y and apply erased_a_Abs.
     rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1.
     rewrite <- app_assoc. eapply H0; eauto. simpl_env. auto.
     eapply erased_lc; eauto.
  - pick fresh y and apply erased_a_Pi; eauto.
     rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1.
     rewrite <- app_assoc. eapply H0; eauto. simpl_env. auto.
     eapply erased_lc; eauto.
  - pick fresh c and apply erased_a_CPi; eauto.
     rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1.
     eapply H0; eauto. eapply erased_lc; eauto.
  - pick fresh c and apply erased_a_CAbs; eauto.
     rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1.
     eapply H0; eauto. eapply erased_lc; eauto.
Qed.


Lemma subst_co_erased : forall W c g a R, lc_co g -> erased_tm W a R -> erased_tm W (co_subst_co_tm g c a) R.
Proof.
  intros W c g a R lc H. generalize dependent g.
  induction H; intros; simpl; eauto.
  - eapply erased_a_Abs with (L := L).
     intros x0 H1.
     rewrite co_subst_co_tm_open_tm_wrt_tm_var; auto 2.
   - eapply erased_a_Pi with (L := L); eauto.
     intros x0 H2.
     rewrite co_subst_co_tm_open_tm_wrt_tm_var; auto 2.
   - eapply erased_a_CPi with (L := union L (singleton c)); eauto.
     intros c0 H4.
     rewrite co_subst_co_tm_open_tm_wrt_co_var; auto 2.
   - eapply erased_a_CAbs with (L := union L (singleton c)); eauto.
     intros c0 H4.
     rewrite co_subst_co_tm_open_tm_wrt_co_var; auto 2.
Qed.

Hint Resolve subst_tm_erased subst_co_erased : erased.

Lemma erased_Pi_some_any: forall W x rho A R1 B R2,
       x `notin` fv_tm_tm_tm B ->
       erased_tm W A R2 ->
       erased_tm ([(x,R1)] ++ W) (open_tm_wrt_tm B (a_Var_f x)) R2 ->
       erased_tm W (a_Pi rho A R1 B) R2.
Proof. intros. apply (erased_a_Pi (union (singleton x) (dom W))); eauto.
       intros. rewrite (tm_subst_tm_tm_intro x B (a_Var_f x0)); auto.
       replace ([(x0,R1)] ++ W) with (nil ++ [(x0,R1)] ++ W); auto.
       assert (uniq ([(x,R1)] ++ W)). {eapply rctx_uniq; eauto. }
       eapply subst_tm_erased. simpl_env. apply erased_app_rctx; eauto.
       econstructor. solve_uniq. auto. auto.
Qed.

Lemma typing_erased_mutual:
    (forall G b A R, Typing G b A R -> erased_tm (ctx_to_rctx G) b R) /\
    (forall G0 phi R  (H : PropWff G0 phi R),
        forall A B T R1, phi = Eq A B T R1 -> erased_tm (ctx_to_rctx G0) A R /\ 
        erased_tm (ctx_to_rctx G0) B R /\ erased_tm (ctx_to_rctx G0) T R) /\
     (forall G0 D p1 p2 R (H : Iso G0 D p1 p2 R), True ) /\
     (forall G0 D A B T R (H : DefEq G0 D A B T R), True) /\
     (forall G0 (H : Ctx G0), True).
Proof. 
  apply typing_wff_iso_defeq_mutual; intros; repeat split; split_hyp; subst; 
  simpl; auto.
  all : try solve [inversion H2; subst; auto].
  all : try solve [econstructor; eauto].
  - eapply erased_sub; eauto.
  - econstructor. apply ctx_to_rctx_uniq; eauto.
  - econstructor. apply ctx_to_rctx_uniq; eauto. 
    eapply ctx_to_rctx_binds_tm; eauto. auto.
  - econstructor; eauto. econstructor; eauto. apply ctx_to_rctx_uniq; eauto. 
  - destruct phi.
    apply (@erased_a_CPi L); try solve [apply (H0 a b A R0); auto]; auto;
    pose H2 := H0 a b A R0 eq_refl; inversion H2 as [H21 [H22 H23]]. 
  - econstructor. apply ctx_to_rctx_uniq; auto. eauto.
  - econstructor; eauto. apply ctx_to_rctx_uniq; eauto.
  - admit.
    Unshelve.
    exact Phm.
Admitted.


Lemma Typing_erased: forall G b A R, Typing G b A R -> 
                                     erased_tm (ctx_to_rctx G) b R.
Proof.
  apply typing_erased_mutual.
Qed.

Hint Resolve Typing_erased : erased.

Lemma toplevel_erased1 : forall W F a A R, binds F (Ax a A R) toplevel -> 
                                           uniq W -> erased_tm W a R.
Proof.
  intros.
  move: (toplevel_closed H) => h0.
  replace W with (nil ++ W ++ nil).
  apply erased_app_rctx. simpl_env; auto.
  simpl_env. pose (P := Typing_erased h0). simpl in P.
  auto. simpl_env. auto.
Qed.
