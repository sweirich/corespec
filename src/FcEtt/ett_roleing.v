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
Require Import FcEtt.param.

Require Export FcEtt.toplevel.


Lemma rctx_uniq : forall W a R, roleing W a R -> uniq W.
Proof. intros W a R H. induction H; eauto.
        - pick fresh x. eapply uniq_app_2; eauto.
        - pick fresh c; eauto.
Qed.

Lemma roleing_app_rctx : forall W1 W2 W3 a R, uniq (W1 ++ W2 ++ W3) -> 
                               roleing (W1 ++ W3) a R ->
                               roleing (W1 ++ W2 ++ W3) a R.
Proof. intros W1 W2 W3 a R U H. generalize dependent W2.
       dependent induction H; intros; eauto.
        - eapply role_a_Abs with (L := union L (dom (W1 ++ W2 ++ W3))).
          intros. rewrite app_assoc.
          eapply H0; eauto. simpl_env. auto.
        - eapply role_a_Pi with (L := union L (dom (W1 ++ W2 ++ W3))); eauto.
          intros. rewrite app_assoc.
          eapply H1; eauto. simpl_env. auto.
        - econstructor; eauto.
Qed.

(* NOTE: we have a database 'roleing' for proving that terms are roleing. *)

(* Tactics concerning roleing terms. *)

Ltac roleing_pick_fresh x :=
  match goal with
    [ |- roleing ?W ?s ?R ] =>
    let v := match s with
             | a_UAbs _ _ => role_a_Abs
             | a_Pi _ _ _ => role_a_Pi
             | a_CPi _ _   => role_a_CPi
             | a_UCAbs _   => role_a_CAbs
             end
    in pick fresh x and apply v
  end.

Ltac roleing_inversion :=
  repeat match goal with
  | [H : roleing _ (a_UAbs _ _) _ |- _ ] =>
    inversion H; subst; clear H
  | [H : roleing _ (a_App _ _ _) _ |- _ ] =>
    inversion H; subst; clear H
  | [H : roleing _ (a_Pi _ _ _) _ |- _ ] =>
    inversion H; subst; clear H
  | [H : roleing _ (a_CPi _ _) _ |- _ ] =>
    inversion H; subst; clear H
  | [H : roleing _ (a_UCAbs _ ) _ |- _ ] =>
    inversion H; subst; clear H
  | [H : roleing _ (a_CApp _ _) _ |- _ ] =>
    inversion H; subst; clear H
end.


Inductive roleing_sort (W : role_context) : sort -> Prop := 
| roleing_Tm : forall a R, roleing W a R -> roleing_sort W (Tm a)
| roleing_Co : forall a b A R, roleing W a R -> roleing W b R -> roleing W A R -> roleing_sort W (Co (Eq a b A R)).

(* Check Forall_forall FIXME:?? *)

Inductive roleing_context : role_context -> context -> Prop :=
 | nil_roleing_ctx : roleing_context nil nil
 | co_roleing_ctx : forall W G c a b A R,
                   roleing_sort W (Co (Eq a b A R)) -> roleing_context W G -> 
                   roleing_context W ([(c, (Co (Eq a b A R)))] ++ G)
 | tm_roleing_ctx : forall W G x A R, roleing_context W G ->
                   roleing_sort W (Tm A) ->
                   roleing_context ([(x,R)] ++ W) ([(x, (Tm A))] ++ G).

Lemma dom_roleing_ctx_rctx_le_ctx : forall W G, roleing_context W G ->
                                               dom W [<=] dom G.
Proof. intros; induction H; simpl; fsetdec.
Qed.

Lemma uniq_roleing_ctx_rctx : forall W G, roleing_context W G -> uniq G
                                          -> uniq W.
Proof. intros. induction H; auto.
       apply IHroleing_context. eapply uniq_app_2; eauto.
       inversion H0. apply IHroleing_context in H4. constructor.
       auto. apply dom_roleing_ctx_rctx_le_ctx in H. fsetdec.
Qed.

Lemma roleing_lc : forall W a R, roleing W a R -> lc_tm a.
intros; induction H; auto.
Qed.

Hint Resolve roleing_lc : lc.

Lemma roleing_sub : forall W a R1 R2, roleing W a R1 -> SubRole R1 R2 ->
                                     roleing W a R2.
Proof. intros W a R1 R2 H S. generalize dependent R2. induction H; intros; eauto.
Qed.

Lemma RolePath_subst : forall F a b Rs x, RolePath a F Rs -> lc_tm b ->
                   RolePath (tm_subst_tm_tm b x a) F Rs.
Proof. intros. induction H; simpl; eauto.
       econstructor; eauto with lngen lc.
Qed.

Lemma RolePath_subst_co : forall F a b Rs c, RolePath a F Rs -> lc_co b ->
                   RolePath (co_subst_co_tm b c a) F Rs.
Proof. intros. induction H; simpl; eauto.
       econstructor; eauto with lngen lc.
Qed.

Lemma subst_tm_roleing : forall W1 x R1 W2 a R b, 
               roleing (W1 ++ [(x,R1)] ++ W2) a R ->
               roleing W2 b R1 -> 
               roleing (W1 ++ W2) (tm_subst_tm_tm b x a) R.
Proof.
  intros W1 x R1 W2 a R b H1 H2. dependent induction H1; simpl; eauto.
  - destruct (x0 == x); auto. 
     + subst. assert (P:R = R1).
       eapply binds_mid_eq; eauto. subst. replace W1 with (nil ++ W1); eauto.
       rewrite <- app_assoc. eapply roleing_app_rctx; simpl_env; eauto.
       eapply roleing_sub; eauto.
     + econstructor. eapply uniq_remove_mid; eauto.
       eapply binds_remove_mid; eauto. eauto.
  - pick fresh y and apply role_a_Abs.
     rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1. eapply roleing_lc; eauto.
     rewrite app_assoc. eapply H0; eauto. simpl_env. auto.
  - pick fresh y and apply role_a_Pi; eauto.
     rewrite tm_subst_tm_tm_open_tm_wrt_tm_var; auto 1. eapply roleing_lc; eauto.
     rewrite app_assoc. eapply H0; eauto. simpl_env. auto.
  - pick fresh c and apply role_a_CPi; eauto.
    rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1. eapply roleing_lc; eauto.
    eapply H0; eauto.
  - pick fresh c and apply role_a_CAbs; eauto.
    rewrite tm_subst_tm_tm_open_tm_wrt_co_var; auto 1. eapply roleing_lc; eauto.
    eapply H0; eauto.
Qed.


Lemma subst_co_roleing : forall W c g a R, lc_co g -> roleing W a R -> roleing W (co_subst_co_tm g c a) R.
Proof.
  intros W c g a R lc H. generalize dependent g.
  induction H; intros; simpl; eauto.
  - eapply role_a_Abs with (L := L).
     intros x0 h1.
     rewrite co_subst_co_tm_open_tm_wrt_tm_var; auto 2.
   - eapply role_a_Pi with (L := L); eauto.
     intros x0 h2.
     rewrite co_subst_co_tm_open_tm_wrt_tm_var; auto 2.
   - eapply role_a_CPi with (L := union L (singleton c)); eauto.
     intros c0 h4.
     rewrite co_subst_co_tm_open_tm_wrt_co_var; auto 2.
   - eapply role_a_CAbs with (L := union L (singleton c)); eauto.
     intros c0 h4.
     rewrite co_subst_co_tm_open_tm_wrt_co_var; auto 2.
Qed.

Hint Resolve subst_tm_roleing subst_co_roleing : roleing.

Lemma roleing_Pi_some_any: forall W x rho A B R2,
       x `notin` fv_tm_tm_tm B ->
       roleing W A R2 ->
       roleing ([(x,Nom)] ++ W) (open_tm_wrt_tm B (a_Var_f x)) R2 ->
       roleing W (a_Pi rho A B) R2.
Proof. intros. apply (role_a_Pi (union (singleton x) (dom W)));
                 eauto using roleing_sub.
       intros. rewrite (tm_subst_tm_tm_intro x B (a_Var_f x0)); auto.
       replace (x0 ~ Nom ++ W) with (nil ++ x0 ~ Nom ++ W); auto.
       assert (uniq ([(x,Nom)] ++ W)). {eapply rctx_uniq; eauto. }
       eapply subst_tm_roleing. simpl_env. apply roleing_app_rctx; eauto.
       econstructor. solve_uniq. auto. auto.
Qed.

Lemma typing_roleing_mutual:
    (forall G b A, Typing G b A -> roleing (ctx_nom G) b Nom) /\
    (forall G0 phi  (H : PropWff G0 phi ),
        forall A B T R', phi = Eq A B T R' -> roleing (ctx_nom G0) A R' /\ 
        roleing (ctx_nom G0) B R' /\ roleing (ctx_nom G0) T Rep) /\
     (forall G0 D p1 p2  (H : Iso G0 D p1 p2 ), True ) /\
     (forall G0 D A B T R (H : DefEq G0 D A B T R), True) /\
     (forall G0 (H : Ctx G0), True).
Proof. 
  apply typing_wff_iso_defeq_mutual; intros; repeat split; split_hyp; subst; 
  simpl; auto.
  all : try solve [inversion H2; subst; eapply roleing_sub; eauto].
  all : try solve [econstructor; eauto].
  all : try solve [eauto using roleing_sub].
  all : try solve [econstructor; eauto using ctx_to_rctx_uniq, ctx_to_rctx_binds_tm].
  - destruct phi. move: (H0 a b A R eq_refl) => ?. split_hyp. clear H0.
    eapply (@role_a_CPi L); eauto.
Qed.


Lemma Typing_roleing: forall G b A, Typing G b A -> 
                                     roleing (ctx_nom G) b Nom.
Proof.
  apply typing_roleing_mutual.
Qed.

Hint Resolve Typing_roleing : roleing.


(*
Lemma toplevel_roleing1 : forall W F a A R, binds F (Ax a A R) toplevel -> 
                                           uniq W -> roleing W a R.
Proof.
  intros.
  move: (toplevel_closed H) => h0.
  replace W with (nil ++ W ++ nil).
  apply roleing_app_rctx. simpl_env; auto.
  simpl_env. pose (P := Typing_roleing h0). simpl in P.
  auto. simpl_env. auto.
Qed. *)
