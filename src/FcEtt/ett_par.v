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

Lemma par_app_rctx : forall S D W1 W2 W3 a a' R, uniq (W1 ++ W2 ++ W3) ->
                     Par S D (W1 ++ W3) a a' R -> 
                     Par S D (W1 ++ W2 ++ W3) a a' R.
Proof. intros S D W1 W2 W3 a a' R U H. generalize dependent W2.
       dependent induction H; intros; eauto.
        - econstructor. eapply erased_app_rctx; eauto.
        - eapply Par_Abs with (L := union L (dom (W1 ++ W2 ++ W3))).
          intros. rewrite <- app_assoc.
          eapply H0; eauto. simpl_env. auto.
        - eapply Par_Pi with (L := union L (dom (W1 ++ W2 ++ W3))); eauto.
          intros. rewrite <- app_assoc.
          eapply H1; eauto. simpl_env. auto.
        - econstructor; eauto.
Qed.

(* ------------------------------------------ *)

(* Synatactic properties about parallel reduction. (Excluding confluence.) *)

(* ------------------------------------------ *)


(* TODO: move these definitions to the OTT file. *)

Inductive multipar S D W ( a : tm) (R : role) : tm -> Prop :=
| mp_refl : multipar S D W a R a
| mp_step : forall b c, Par S D W a b R -> multipar S D W b R c -> multipar S D W a R c.

Hint Constructors multipar.


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
(*
Ltac erased_case :=
  let x := fresh in
  let h0 := fresh in
  erased_pick_fresh x; eauto using lc_erase;
  match goal with
    [ H : forall x, erased_tm (erase (open_tm_wrt_tm ?b (a_Var_f x)) ?R) ?R |- _ ] =>
    move: (H x) => h0; rewrite <- open_tm_erase_tm in h0; eauto
  | [ H : ∀ c, erased_tm (erase (open_tm_wrt_co ?b (g_Var_f c)) ?R) ?R |- _ ] =>
    move: (H x) => h0; rewrite <- open_co_erase_tm2 with (g := (g_Var_f x)) in h0; auto
  end.


Lemma erased_tm_erase_mutual : forall R0,
  (forall a, lc_tm a -> erased_tm (erase a R0) R0)
  /\ (forall a, lc_brs a -> True)
  /\ (forall a, lc_co a -> True)
  /\ (forall phi, lc_constraint phi -> forall a b A R, phi = (Eq a b A R) ->
                                         erased_tm (erase a R0) R0 /\ erased_tm (erase b R0) R0
                                         /\ erased_tm (erase A R0) R0).

Proof. intro.
  apply lc_tm_lc_brs_lc_co_lc_constraint_mutind; intros; simpl; eauto.
  all: try solve [ try (destruct rho); simpl; eauto].
  all: try solve [erased_case].
  - destruct R, R0; auto. simpl. constructor; auto. apply rep_nsub_nom.
  - destruct phi. destruct (H _ _ _ _ eq_refl) as (h0 & h1 & h2). simpl.
    erased_case.
  - inversion H2. subst. tauto.
    Unshelve. all:auto.
Qed.

Lemma erased_tm_erase : forall R a, lc_tm a -> erased_tm (erase a R) R.
Proof.
  intros.
  destruct erased_tm_erase_mutual with R.
  eauto.
Qed.

Hint Resolve erased_tm_erase : erased. Locate multipar.
*)
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

Definition joins S D W a b R := exists c, erased_tm W a R /\ erased_tm W b R /\
                               multipar S D W a R c /\ multipar S D W b R c.


Lemma erased_lc : forall W a R, erased_tm W a R -> lc_tm a.
intros; induction H; auto.
Qed.

Hint Resolve erased_lc : lc.

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
     + econstructor. eapply uniq_remove_mid; eauto.
       eapply binds_remove_mid; eauto.
  - pick fresh y and apply erased_a_Abs.
     assert(P : a_Var_f y = tm_subst_tm_tm b x (a_Var_f y)).
     {rewrite tm_subst_tm_tm_fresh_eq; auto. }
     rewrite P.
     rewrite <- tm_subst_tm_tm_open_tm_wrt_tm; auto.
     rewrite <- app_assoc. eapply H0; eauto. simpl_env. auto.
     eapply erased_lc; eauto.
  - pick fresh y and apply erased_a_Pi; eauto.
     assert(P : a_Var_f y = tm_subst_tm_tm b x (a_Var_f y)).
     {rewrite tm_subst_tm_tm_fresh_eq; auto. }
     rewrite P.
     rewrite <- tm_subst_tm_tm_open_tm_wrt_tm; auto.
     rewrite <- app_assoc. eapply H0; eauto. simpl_env. auto.
     eapply erased_lc; eauto.
  - pick fresh c and apply erased_a_CPi; eauto.
     assert(P : g_Var_f c = tm_subst_tm_co b x (g_Var_f c)).
     {rewrite tm_subst_tm_co_fresh_eq; auto. }
     rewrite P.
     rewrite <- tm_subst_tm_tm_open_tm_wrt_co; auto.
     eapply H0; eauto. eapply erased_lc; eauto.
  - pick fresh c and apply erased_a_CAbs; eauto.
     assert(P : g_Var_f c = tm_subst_tm_co b x (g_Var_f c)).
     {rewrite tm_subst_tm_co_fresh_eq; auto. }
     rewrite P.
     rewrite <- tm_subst_tm_tm_open_tm_wrt_co; auto.
     eapply H0; eauto. eapply erased_lc; eauto.
Qed.


Lemma subst_co_erased : forall W c g a R, lc_co g -> erased_tm W a R -> erased_tm W (co_subst_co_tm g c a) R.
Proof.
  intros W c g a R lc H. generalize dependent g.
  induction H; intros; simpl; eauto.
  - eapply erased_a_Abs with (L := L).
     intros x0 H1.
     assert(P : a_Var_f x0 = co_subst_co_tm g c (a_Var_f x0)).
     {rewrite co_subst_co_tm_fresh_eq; auto. }
     rewrite P.
     rewrite <- co_subst_co_tm_open_tm_wrt_tm; auto.
   - eapply erased_a_Pi with (L := L); eauto.
     intros x0 H2.
     assert(P : a_Var_f x0 = co_subst_co_tm g c (a_Var_f x0)).
     {rewrite co_subst_co_tm_fresh_eq; auto. }
     rewrite P.
     rewrite <- co_subst_co_tm_open_tm_wrt_tm; auto.
   - eapply erased_a_CPi with (L := union L (singleton c)); eauto.
     intros c0 H4.
     assert(P : g_Var_f c0 = co_subst_co_co g c (g_Var_f c0)).
     {rewrite co_subst_co_co_fresh_eq; auto. } 
     rewrite P.
     rewrite <- co_subst_co_tm_open_tm_wrt_co; auto.
   - eapply erased_a_CAbs with (L := union L (singleton c)); eauto.
     intros c0 H4.
     assert(P : g_Var_f c0 = co_subst_co_co g c (g_Var_f c0)).
     {rewrite co_subst_co_co_fresh_eq; auto. } 
     rewrite P.
     rewrite <- co_subst_co_tm_open_tm_wrt_co; auto.
Qed.

Hint Resolve subst_tm_erased subst_co_erased : erased.

Lemma Par_lc1 : forall G D W a a' R , Par G D W a a' R -> lc_tm a.
  intros.  induction H; auto. eapply erased_lc; eauto.
Qed.

(* FIXME: find a good place for this tactic. *)
(* cannot move this to ett_ind.v because need Toplevel_lc ??? *)
Ltac lc_toplevel_inversion :=
  match goal with
  | [ b : binds ?F _ toplevel |- _ ] =>
    apply Toplevel_lc in b; inversion b; auto
end.

Lemma Par_lc2 : forall G D W a a' R, Par G D W a a' R -> lc_tm a'.
Proof.
  intros. induction H; auto.
  - lc_solve.
  - lc_solve.
  - lc_solve.
  - lc_toplevel_inversion.
  - inversion IHPar1. constructor; auto.
  - inversion IHPar. constructor; auto.
Qed.

Hint Resolve Par_lc1 Par_lc2 : lc.

Lemma typing_erased_mutual:
    (forall G b A R, Typing G b A R -> erased_tm (ctx_to_rctx G) b R) /\
    (forall G0 phi (H : PropWff G0 phi),
        forall A B T R, phi = Eq A B T R -> erased_tm (ctx_to_rctx G0) A R /\ 
        erased_tm (ctx_to_rctx G0) B R /\ erased_tm (ctx_to_rctx G0) T R) /\
     (forall G0 D p1 p2 (H : Iso G0 D p1 p2), True ) /\
     (forall G0 D A B T R (H : DefEq G0 D A B T R), True) /\
     (forall G0 (H : Ctx G0), True).
Proof. 
  apply typing_wff_iso_defeq_mutual; intros; repeat split; split_hyp; subst; 
  simpl; auto.
  all : try solve [inversion H2; subst; auto].
  all : try solve [econstructor; eauto].
  - econstructor. apply ctx_to_rctx_uniq; eauto.
  - econstructor. apply ctx_to_rctx_uniq; eauto. 
    eapply ctx_to_rctx_binds_tm; eauto.
  - econstructor; eauto. econstructor. apply ctx_to_rctx_uniq.
    eapply Typing_Ctx; eauto.
  - destruct phi.
    apply (@erased_a_CPi L); try solve [apply (H0 a b A R0); auto]; auto;
    pose H2 := H0 a b A R0 eq_refl; inversion H2 as [H21 [H22 H23]]; econstructor; eassumption.
  - econstructor. apply ctx_to_rctx_uniq. auto.
Qed.


Lemma Typing_erased: forall G b A R, Typing G b A R -> 
                                     erased_tm (ctx_to_rctx G) b R.
Proof.
  apply typing_erased_mutual.
Qed.

Hint Resolve Typing_erased : erased.
(*

Lemma typing_erased_type_mutual:
    (forall G b A R, Typing G b A R -> erased_tm (ctx_to_rctx G) A R) /\
    (forall G0 phi (H : PropWff G0 phi), True) /\
     (forall G0 D p1 p2 (H : Iso G0 D p1 p2), True ) /\
     (forall G0 D A B T R (H : DefEq G0 D A B T R), True) /\
     (forall G0 (H : Ctx G0), erased_context (ctx_to_rctx G0) G0).
Proof.
  apply typing_wff_iso_defeq_mutual; intros; repeat split; split_hyp; subst; simpl; auto.
  all: eauto using Typing_erased.
    all: try solve [inversion H; pick fresh x;
      rewrite (tm_subst_tm_tm_intro x); auto;
        eapply subst_tm_erased;
        eauto using Typing_erased].
  - induction H. 
     + inversion b.
     + inversion b. inversion H1.
       simpl in H1. apply IHerased_context; auto.
       inversion c; auto.
     + inversion b. 
        * inversion H1; subst. inversion H0; subst.
          assert (P : [(x,R)] = nil ++ [(x,R)]). { auto. }
          rewrite P. rewrite app_assoc. apply erased_app_rctx; eauto.
          apply Ctx_uniq in c. simpl_env. apply dom_erased_ctx_rctx_le_ctx in H.
          inversion c. constructor. eapply rctx_uniq; eauto. fsetdec.
        * assert (P : [(x0,R0)] = nil ++ [(x0,R0)]). { auto. }
          rewrite P. rewrite app_assoc. apply erased_app_rctx; auto.
          simpl_env. apply dom_erased_ctx_rctx_le_ctx in H.
          inversion c. constructor. eapply rctx_uniq; eauto. fsetdec.
          simpl_env. inversion c. apply IHerased_context; eauto.
  - inversion H; subst. apply Typing_erased in t0.
    pick fresh x. rewrite (tm_subst_tm_tm_intro x); auto.
    replace (ctx_to_rctx G) with (nil ++ (ctx_to_rctx G)); auto.
    eapply subst_tm_erased; eauto.
  - inversion H; pick fresh x;
      rewrite (co_subst_co_tm_intro x); auto.
        eapply subst_co_erased;
        eauto using Typing_erased.
  - apply Forall_forall.
    intros s h0. destruct s.
    destruct h0. inversion H1. econstructor.
    eauto using Typing_erased.
    eapply Forall_forall in H; eauto. simpl in H. auto.
  - apply Forall_forall.
    intros s h0. destruct s. inversion p. subst.
    destruct h0. inversion H4. econstructor;  eauto using Typing_erased.
    eapply Forall_forall in H; eauto. simpl in H. auto.
Qed.

Lemma Typing_erased_type : forall G b A R, Typing G b A R -> erased_tm A.
Proof. apply typing_erased_type_mutual. Qed.

Hint Resolve Typing_erased_type : erased.
*)
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
(*
Lemma toplevel_erased2 : forall F a A R, binds F (Ax a A R) toplevel -> erased_tm A.
Proof.
  intros.
  move: (toplevel_closed H) => h0.
  eauto with erased.
Qed.

Hint Resolve toplevel_erased1 toplevel_erased2 : erased.
*)
(*
(* Introduce a hypothesis about an erased opened term. *)
Ltac erased_body x Ea :=
    match goal with
      [ H4 : ∀ x : atom, x `notin` ?L0 → erased_tm (open_tm_wrt_tm ?a (a_Var_f x))
                         |- _ ] =>
      move: (H4 x ltac:(auto)) => Ea; clear H4
    end.

(* Move this to ett_ind? *)
Ltac eta_eq y EQ :=
   match goal with
      [ H :
          ∀ x : atom,
            x `notin` ?L → open_tm_wrt_tm ?a (a_Var_f x) =
                           a_App ?b ?rho _ _ |- _ ] =>
   move: (H y ltac:(auto)) =>  EQ
end.
*)

Lemma Par_erased_tm_fst : forall G D W a a' R, Par G D W a a' R -> 
                                               erased_tm W a R.
Proof. intros G D W a a' R H. induction H; eauto.
Qed.

Lemma Par_erased_tm_snd : forall G D W a a' R, Par G D W a a' R ->
                                               erased_tm W a' R.
Proof. intros G D W a a' R H. induction H; eauto.
        - inversion IHPar1; subst. pick fresh x.
          assert (Q : tm_subst_tm_tm b' x (a_Var_f x) = b').
          { simpl; destruct (@eq_dec tmvar _ x x); try done. }
          rewrite <- Q. assert (P : tm_subst_tm_tm b' x a' = a').
          { eapply tm_subst_tm_tm_fresh_eq; eauto. }
          rewrite <- P. rewrite <- tm_subst_tm_tm_open_tm_wrt_tm.
          replace W with (W ++ nil); auto. eapply subst_tm_erased; eauto.
          simpl_env. auto. eapply erased_lc; eauto.
        - inversion IHPar; subst. pick fresh c.
          assert (Q : co_subst_co_co g_Triv c (g_Var_f c) = g_Triv).
          { simpl; destruct (@eq_dec covar _ c c); try done. }
          rewrite <- Q. assert (P : co_subst_co_tm g_Triv c a' = a').
          { eapply co_subst_co_tm_fresh_eq; eauto. }
          rewrite <- P. rewrite <- co_subst_co_tm_open_tm_wrt_co.
          replace W with (W ++ nil); auto. eapply subst_co_erased; eauto.
          simpl_env. auto. auto.
        - admit.
        - inversion IHPar1; eauto.
        - inversion IHPar; eauto.
Admitted.
(*
Lemma Par_erased_tm : forall G D a a' R, Par G D a a' R -> erased_tm a -> erased_tm a'.
Proof.
  intros G D a a' R Ep Ea.  induction Ep; inversion Ea; subst; eauto 2.
  all: try solve [ erased_pick_fresh x; auto ].
  all: eauto.
  - move: (IHEp1 ltac:(auto)); inversion 1;
    pick fresh x;
    rewrite (tm_subst_tm_tm_intro x); auto;
    apply subst_tm_erased; auto.
  - move: (IHEp ltac:(auto)); inversion 1;
    pick fresh x;
    rewrite (co_subst_co_tm_intro x); auto;
    apply subst_co_erased; auto.
  - eauto with erased.
  - constructor. apply IHEp1 in H2. inversion H2; subst.
    constructor. auto. constructor. eauto.
  - constructor. constructor. apply IHEp in H0. inversion H0. auto.
Qed.

Hint Resolve Par_erased_tm : erased.

(* ------------------------------------------------------------- *)

Lemma Par_sub: forall S D a a' R1 R2, Par S D a a' R1 -> SubRole R1 R2 ->
                                      Par S D a a' R2.
Proof. intros S D a a' R1 R2 H SR. generalize dependent R2.
       induction H; intros; simpl; eauto.
Qed.
*)

Lemma subst1 : forall b S D W W' a a' R1 R2 x, Par S D W a a' R1 -> 
               erased_tm (W ++ [(x,R1)] ++ W') b R2 ->
               Par S D (W ++ W') (tm_subst_tm_tm a x b) (tm_subst_tm_tm a' x b) R2.
Proof.
  intros b S D W W' a a' R1 R2 x PAR ET.
  dependent induction ET; intros; simpl; auto.
   - constructor. constructor. eapply uniq_remove_mid; eauto.
   - constructor. constructor. eapply uniq_remove_mid; eauto.
   - destruct (x0 == x); auto. 
     + subst. assert (P:R = R1).
       eapply binds_mid_eq; eauto. subst. replace W' with (W' ++ nil); eauto.
       eapply par_app_rctx. simpl_env. eapply uniq_remove_mid; eauto.
       simpl_env; eauto. 
     + econstructor. econstructor. eapply uniq_remove_mid; eauto.
       eapply binds_remove_mid; eauto.
   - eapply Par_Abs with (L := union L (singleton x)).
     intros x0 H1.
     assert(P : a_Var_f x0 = tm_subst_tm_tm a x (a_Var_f x0)).
     {rewrite tm_subst_tm_tm_fresh_eq; auto. }
     assert(Q : a_Var_f x0 = tm_subst_tm_tm a' x (a_Var_f x0)).
     {rewrite tm_subst_tm_tm_fresh_eq; auto. }
     rewrite P.
     rewrite <- tm_subst_tm_tm_open_tm_wrt_tm; auto.
     rewrite <- P. rewrite Q.
     rewrite <- tm_subst_tm_tm_open_tm_wrt_tm; auto.
     rewrite <- Q. simpl_env. eapply H0; eauto. simpl_env. auto.
     eapply Par_lc2; eauto. eapply Par_lc1; eauto.
   - econstructor; eauto.
   - eapply Par_Pi with (L := union L (singleton x)); eauto.
     intros x0 H1.
     assert(P : a_Var_f x0 = tm_subst_tm_tm a x (a_Var_f x0)).
     {rewrite tm_subst_tm_tm_fresh_eq; auto. }
     assert(Q : a_Var_f x0 = tm_subst_tm_tm a' x (a_Var_f x0)).
     {rewrite tm_subst_tm_tm_fresh_eq; auto. }
     rewrite P.
     rewrite <- tm_subst_tm_tm_open_tm_wrt_tm; auto.
     rewrite <- P. rewrite Q.
     rewrite <- tm_subst_tm_tm_open_tm_wrt_tm; auto.
     rewrite <- Q. simpl_env. eapply H0; eauto. simpl_env. auto.
     eapply Par_lc2; eauto. eapply Par_lc1; eauto.
   - eapply Par_CPi with (L := union L (singleton x)); eauto.
     intros c H1.
     assert(P : g_Var_f c = tm_subst_tm_co a x (g_Var_f c)).
     {rewrite tm_subst_tm_co_fresh_eq; auto. }
     assert(Q : g_Var_f c = tm_subst_tm_co a' x (g_Var_f c)).
     {rewrite tm_subst_tm_co_fresh_eq; auto. }
     rewrite P.
     rewrite <- tm_subst_tm_tm_open_tm_wrt_co; auto.
     rewrite <- P. rewrite Q.
     rewrite <- tm_subst_tm_tm_open_tm_wrt_co; auto.
     rewrite <- Q. eapply H0; eauto.
     eapply Par_lc2; eauto. eapply Par_lc1; eauto.
   - eapply Par_CAbs with (L := union L (singleton x)); eauto.
     intros c H1.
     assert(P : g_Var_f c = tm_subst_tm_co a x (g_Var_f c)).
     {rewrite tm_subst_tm_co_fresh_eq; auto. }
     assert(Q : g_Var_f c = tm_subst_tm_co a' x (g_Var_f c)).
     {rewrite tm_subst_tm_co_fresh_eq; auto. }
     rewrite P.
     rewrite <- tm_subst_tm_tm_open_tm_wrt_co; auto.
     rewrite <- P. rewrite Q.
     rewrite <- tm_subst_tm_tm_open_tm_wrt_co; auto.
     rewrite <- Q. eapply H0; eauto.
     eapply Par_lc2; eauto. eapply Par_lc1; eauto.
   - econstructor; eauto.
   - econstructor; eauto.
   - econstructor; eauto.
   - econstructor; eauto.
Qed.

Lemma open1 : forall b S D a a' L, Par S D a a'
  -> (forall x, x `notin` L -> erased_tm (open_tm_wrt_tm b (a_Var_f x)))
  -> Par S D (open_tm_wrt_tm b a) (open_tm_wrt_tm b a').
Proof.
  intros.
  pick fresh x.
  rewrite (tm_subst_tm_tm_intro x); auto.
  rewrite [(_ _ a')] (tm_subst_tm_tm_intro x); auto.
  apply subst1; auto.
Qed.
*)

Lemma subst2 : forall S D b x, lc_tm b ->
  forall a a' R, Par S D a a' R -> Par S D (tm_subst_tm_tm b x a) (tm_subst_tm_tm b x a') R.
Proof.
  intros S D b x EB a a' R PAR.
  induction PAR; simpl.
  all: eauto using tm_subst_tm_tm_lc_tm.
  all: autorewrite with subst_open; auto.
  all: try solve [Par_pick_fresh y; autorewrite with subst_open_var; eauto].
  - rewrite tm_subst_tm_tm_fresh_eq.
    eapply Par_Axiom; eauto.
    match goal with
    | [H : binds ?c ?phi ?G |- _ ] =>
      move:  (toplevel_closed H) => h0
    end.
    move: (Typing_context_fv h0) => ?. split_hyp.
    simpl in *.
    fsetdec.
Qed.

(*
Lemma subst3 : forall S D b b' x R,
    Par S D b b' R ->
    forall a a', erased_tm a R -> Par S D a a' R ->
    Par S D (tm_subst_tm_tm b x a) (tm_subst_tm_tm b' x a') R.
Proof.
  intros.
  dependent induction H1; simpl; eauto 2; erased_inversion; eauto 4.
  all: try solve [ Par_pick_fresh y;
              autorewrite with subst_open_var; eauto 3 with lc ].
  all: try solve [ autorewrite with subst_open; eauto 4 with lc ].
  - apply subst1; auto.
  - eapply Par_Axiom; eauto.
    rewrite tm_subst_tm_tm_fresh_eq. eauto.
    match goal with
    | [H : binds ?c ?phi ?G |- _ ] =>
      move:  (toplevel_closed H) => h0
    end.
     move: (Typing_context_fv h0) => ?. split_hyp.
     fsetdec. 
Qed.
*)

Lemma subst4 : forall S D b x, lc_co b ->
    forall a a' R, Par S D a a' R ->
    Par S D (co_subst_co_tm b x a) (co_subst_co_tm b x a') R.
Proof.
  intros S D b x EB a a' R PAR.
  induction PAR; simpl; auto.
  all: try solve [ Par_pick_fresh y;
              autorewrite with subst_open_var; eauto 3 with lc ].
  all: try solve [ autorewrite with subst_open; eauto 4 with lc ].
  - apply Par_Refl. eapply co_subst_co_tm_lc_tm; auto.
  - rewrite co_subst_co_tm_fresh_eq. eauto.
    match goal with
    | [H : binds ?c ?phi ?G |- _ ] =>
      move:  (toplevel_closed H) => h0
    end.
    move: (Typing_context_fv  h0) => ?. split_hyp.
    simpl in *.
    fsetdec.
Qed.
(*
Lemma multipar_subst3 : forall S D b b' x R, erased_tm b R ->
    multipar S D b b' R ->
    forall a a', erased_tm a R -> multipar S D a a' R ->
    multipar S D (tm_subst_tm_tm b x a) (tm_subst_tm_tm b' x a') R.
Proof.
  intros S D b b' x R lc H.
  dependent induction H; auto.
  - intros a0 a' lc2 H.
    dependent induction H; auto.
    apply (@mp_step _ _ _ _ ((tm_subst_tm_tm a x b))); auto.
    apply subst3; auto.
    apply Par_Refl; eapply erased_lc; eauto.
    apply IHmultipar.
    eapply Par_erased_tm; eauto.
  - intros a0 a' lc2 H1.
    dependent induction H1; auto.
    apply (@mp_step _ _ _ _ (tm_subst_tm_tm b x a0)); auto.
    apply subst3; auto.
    apply Par_Refl; eapply erased_lc; eauto.
    apply IHmultipar; auto.
    eapply Par_erased_tm; eauto.
    apply (@mp_step _ _ _ _ ((tm_subst_tm_tm a x b0))); auto.
    apply subst2; auto.
    eapply Par_lc1; eauto.
    apply IHmultipar0; auto.
    eapply Par_erased_tm; eauto.
Qed.
*)
Lemma multipar_subst4 : forall S D b x, lc_co b ->
    forall a a' R, multipar S D a a' R ->
    multipar S D (co_subst_co_tm b x a) (co_subst_co_tm b x a') R.
Proof.
  intros S D b x H a a' R H0.
  dependent induction H0; eauto.
  apply (@mp_step _ _ _ R (co_subst_co_tm b x b0)); auto.
  apply subst4; auto.
Qed.
(*
Lemma erased_tm_open_tm_wrt_tm: forall a x, erased_tm a -> erased_tm (open_tm_wrt_tm a (a_Var_f x)).
Proof.
  intros a x H.
  pose K := erased_lc H.
  rewrite open_tm_wrt_tm_lc_tm; eauto.
Qed.

Hint Resolve erased_tm_open_tm_wrt_tm : erased.
*)

Lemma Par_Pi_exists: ∀ x (G : context) D rho (A B A' B' : tm) R R',
    x `notin` fv_tm_tm_tm B -> Par G D A A' R
    → Par G D (open_tm_wrt_tm B (a_Var_f x)) B' R'
    → Par G D (a_Pi rho A R B) (a_Pi rho A' R (close_tm_wrt_tm x B')) R'.
Proof.
  intros x G D rho A B A' B' R R' H H0 H1. 
  apply (Par_Pi (fv_tm_tm_tm B)); eauto.
  intros x0 h0.
  rewrite -tm_subst_tm_tm_spec.
  rewrite (tm_subst_tm_tm_intro x B (a_Var_f x0)); auto.
  apply subst2; auto.
Qed.

Lemma Par_CPi_exists:  ∀ c (G : context) D (A B a A' B' a' T T': tm) R R',
       c `notin` fv_co_co_tm a -> Par G D A A' R
       → Par G D B B' R -> Par G D T T' R
         → Par G D (open_tm_wrt_co a (g_Var_f c)) (a') R'
         → Par G D (a_CPi (Eq A B T R) a) (a_CPi (Eq A' B' T' R) (close_tm_wrt_co c a')) R'.
Proof.
  intros c G D A B a A' B' a' T T' R R' H H0 H1 h0 H2.
  apply (Par_CPi (singleton c)); auto.
  intros c0 H3.
  rewrite -co_subst_co_tm_spec.
  rewrite (co_subst_co_tm_intro c  a (g_Var_f c0));  auto.
  apply subst4; auto.
Qed.


Lemma Par_Abs_exists: ∀ x (G : context) D rho R R' (a a' : tm),
    x `notin` fv_tm_tm_tm a
    → Par G D (open_tm_wrt_tm a (a_Var_f x)) a' R'
    → Par G D (a_UAbs rho R a) (a_UAbs rho R (close_tm_wrt_tm x a')) R'.
Proof.
  intros x G D rho R R' a a' hi0 H0.
  apply (Par_Abs (singleton x)); eauto.
  intros x0 h0.
  rewrite -tm_subst_tm_tm_spec.
  rewrite (tm_subst_tm_tm_intro x a (a_Var_f x0)); auto.
  apply subst2; auto.
Qed.

Lemma Par_CAbs_exists: forall c (G : context) D (a a': tm) R,
       c `notin` fv_co_co_tm a
       -> Par G D (open_tm_wrt_co a (g_Var_f c)) a' R
       → Par G D (a_UCAbs a) (a_UCAbs (close_tm_wrt_co c a')) R.
Proof.
  intros c G D a a' R H H0.
  apply (Par_CAbs (singleton c)); auto.
  intros c0 H3.
  rewrite -co_subst_co_tm_spec.
  rewrite (co_subst_co_tm_intro c  a (g_Var_f c0));  auto.
  apply subst4; auto.
Qed.

Lemma Par_open_tm_wrt_co_preservation: forall G D B1 B2 c R, Par G D (open_tm_wrt_co B1 (g_Var_f c)) B2 R -> exists B', B2 = open_tm_wrt_co B' (g_Var_f c) /\ Par G D (open_tm_wrt_co B1 (g_Var_f c)) (open_tm_wrt_co B' (g_Var_f c)) R.
Proof.
  intros G D B1 B2 c R H.
  exists (close_tm_wrt_co c B2).
  have:open_tm_wrt_co (close_tm_wrt_co c B2) (g_Var_f c) = B2 by apply open_tm_wrt_co_close_tm_wrt_co.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.

Lemma Par_open_tm_wrt_tm_preservation: forall G D B1 B2 x R, Par G D (open_tm_wrt_tm B1 (a_Var_f x)) B2 R -> exists B', B2 = open_tm_wrt_tm B' (a_Var_f x) /\ Par G D (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)) R.
Proof.
  intros G D B1 B2 x R H.
  exists (close_tm_wrt_tm x B2).
  have:open_tm_wrt_tm (close_tm_wrt_tm x B2) (a_Var_f x) = B2 by apply open_tm_wrt_tm_close_tm_wrt_tm.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.

Lemma multipar_Pi_exists: ∀ x (G : context) D rho (A B A' B' : tm) R R',
       lc_tm (a_Pi rho A R B) -> x `notin` fv_tm_tm_tm B -> multipar G D A A' R
       → multipar G D (open_tm_wrt_tm B (a_Var_f x)) B' R'
       → multipar G D (a_Pi rho A R B) (a_Pi rho A' R (close_tm_wrt_tm x B')) R'.
Proof.
  intros x G D rho A B A' B' R R' lc e H H0.
  dependent induction H; eauto.
  - dependent induction H0; eauto.
      by rewrite close_tm_wrt_tm_open_tm_wrt_tm; auto.
    apply (@mp_step _ _ _ _ (a_Pi rho a R (close_tm_wrt_tm x b))); auto.
    + inversion lc; subst; clear lc.
      apply (Par_Pi (singleton x)); auto.
      intros x0 H1.
      rewrite -tm_subst_tm_tm_spec.
      rewrite (tm_subst_tm_tm_intro x B (a_Var_f x0)); auto.
      apply subst2; auto.
    + apply IHmultipar; auto.
      * inversion lc; subst; clear lc.
        constructor; eauto.
        intros x0.
        rewrite -tm_subst_tm_tm_spec.
        apply tm_subst_tm_tm_lc_tm; auto.
        apply Par_lc2 in H; auto.
      * rewrite fv_tm_tm_tm_close_tm_wrt_tm_rec.
        fsetdec.
      * rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.
  - apply (@mp_step _ _ _ _ (a_Pi rho b R B)); auto.
     + apply (Par_Pi (singleton x)); auto.
       intros x0 H2.
       inversion lc; subst; clear lc; auto.
     + apply IHmultipar; auto.
       inversion lc; subst; clear lc.
       constructor; auto.
       apply Par_lc2 in H; auto.
Qed.

Lemma multipar_Pi_A_proj: ∀ (G : context) D rho (A B A' B' : tm) R R',
    lc_tm A -> multipar G D (a_Pi rho A R B) (a_Pi rho A' R B') R'
    -> multipar G D A A' R.
Proof.
  intros G D rho A B A' B' R R' h0 h1.
  dependent induction h1; eauto.
  inversion H; subst.
  eapply IHh1; eauto.
  apply (@mp_step _ _ _ _ A'0); auto.
  eapply IHh1; eauto.
  eapply Par_lc2; eauto 1.
Qed.

Lemma multipar_Pi_B_proj: ∀ (G : context) D rho (A B A' B' : tm) R R',
    multipar G D (a_Pi rho A R B) (a_Pi rho A' R B') R'
    → (exists L, forall x, x `notin` L -> multipar G D (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)) R').
Proof.
  intros G D rho A B A' B' R R' h1.
  dependent induction h1; eauto.
  Unshelve.
  inversion H; subst.
  eapply IHh1; eauto.
  destruct (IHh1 rho A'0 B'0 A' B' R) as [L0 h0]; auto.
  exists (L \u L0); eauto.
  apply (fv_tm_tm_tm A').
Qed.


Lemma multipar_CPi_exists:  ∀ c (G : context) D (A B a T A' B' a' T': tm) R R',
       lc_tm (a_CPi (Eq A B T R) a) -> c `notin` fv_co_co_tm a -> multipar G D A A' R
       → multipar G D B B' R -> multipar G D T T' R
         → multipar G D (open_tm_wrt_co a (g_Var_f c)) a' R'
         → multipar G D (a_CPi (Eq A B T R) a) (a_CPi (Eq A' B' T' R) (close_tm_wrt_co c a')) R'.
Proof.
  intros c G D A B a T A' B' a' T' R R' lc e H H0 H2 H1.
  dependent induction H; eauto 1.
  - dependent induction H0; eauto 1.
    + dependent induction H1; eauto 1.
      * dependent induction H2; eauto 1.
        rewrite close_tm_wrt_co_open_tm_wrt_co; auto.
        inversion lc; subst.
        inversion H3; subst.
        apply mp_step with (b:= (a_CPi (Eq a0 a1 b R) a)); eauto.
        apply IHmultipar; auto.
        apply (lc_a_CPi_exists c); auto.
        constructor; eauto.
        eapply Par_lc2; eauto.
      * eapply mp_step with (b:= (a_CPi (Eq a0 a1 T R) (close_tm_wrt_co c b))); eauto.
        -- inversion lc; subst; clear lc.
           inversion H4; subst; clear H4.
           apply (Par_CPi (singleton c)); auto.
           intros c1 H0.
           rewrite -co_subst_co_tm_spec.
           rewrite (co_subst_co_tm_intro c a (g_Var_f c1)); auto.
           apply subst4; auto.
        -- apply IHmultipar; eauto.
           ++ inversion lc; subst; clear lc.
              constructor; eauto 1.
              intros c1.
              rewrite -co_subst_co_tm_spec.
              apply co_subst_co_tm_lc_tm; auto.
              apply Par_lc2 in H; auto.
           ++ rewrite fv_co_co_tm_close_tm_wrt_co_rec.
              fsetdec.
           ++ rewrite open_tm_wrt_co_close_tm_wrt_co; auto.
      + eapply mp_step with (b:= (a_CPi (Eq a0 b T R) a)); eauto.
        -- inversion lc; subst; clear lc.
           inversion H5; subst; clear H5.
           apply (Par_CPi (singleton c)); auto.
        -- apply IHmultipar; eauto.
           inversion lc; subst.
           apply lc_a_CPi; eauto.
           inversion H5; subst.
           constructor; eauto.
           eapply Par_lc2; eauto.
  - apply mp_step with (b:= (a_CPi (Eq b B T R) a)); auto.
    inversion lc; subst.
    inversion H6; subst.
      by apply (Par_CPi (singleton c)); auto.
     apply IHmultipar; auto.
     inversion lc; subst; clear lc.
     constructor; auto.
     constructor; auto.
     apply Par_lc2 in H; auto.
     inversion H6; auto.
     inversion H6; auto.
     Unshelve. apply (fv_co_co_tm a).
Qed.

Lemma multipar_CPi_B_proj:  ∀ (G : context) D (A B a A' B' a' T T': tm) R R',
    multipar G D (a_CPi (Eq A B T R) a) (a_CPi (Eq A' B' T' R) a') R'
  → (exists L, forall c, c `notin` L -> multipar G D (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co a' (g_Var_f c)) R').
Proof.
  intros G D A B a A' B' a' T T' R R' h1.
  dependent induction h1; eauto.
  Unshelve.
  inversion H; subst.
  eapply IHh1; eauto.
  destruct (IHh1 A'0 B'0 a'0 A' B' a' A1' T' R) as [L0 h0]; auto.
  exists (L \u L0); eauto.
  apply (fv_tm_tm_tm A').
Qed.

Lemma multipar_CPi_phi_proj:  ∀ (G : context) D (A B a A' B' a' T T': tm) R R',
    multipar G D (a_CPi (Eq A B T R) a) (a_CPi (Eq A' B' T' R) a') R'
    -> (multipar G D A A' R /\ multipar G D B B' R /\ multipar G D T T' R).
Proof.
  intros G D A B a A' B' a' T T' R R' H.
  dependent induction H; eauto.
  inversion H; subst.
  eapply IHmultipar; eauto.
  repeat split; eauto.
  apply mp_step with (b := A'0); auto.
  destruct (IHmultipar A'0 B'0 a'0 A' B' a' A1' T' R); auto.
  destruct (IHmultipar A'0 B'0 a'0 A' B' a' A1' T' R); auto.
  apply mp_step with (b:= B'0); auto.
  apply H2.
  destruct (IHmultipar A'0 B'0 a'0 A' B' a' A1' T' R); auto.
  apply mp_step with (b:= A1'); auto.
  apply H2.
Qed.

Lemma multipar_Abs_exists: ∀ x (G : context) D rho R R' (a a' : tm),
       lc_tm (a_UAbs rho R a) -> x `notin` fv_tm_tm_tm a
       → multipar G D (open_tm_wrt_tm a (a_Var_f x)) a' R'
       → multipar G D (a_UAbs rho R a) (a_UAbs rho R (close_tm_wrt_tm x a')) R'.
Proof.
  intros x G D rho R R' B B' lc e H.
  dependent induction H; eauto 2.
  - autorewrite with lngen. eauto 2.
  - assert (Par G D (a_UAbs rho R B) (a_UAbs rho R (close_tm_wrt_tm x b)) R0).
    eapply (Par_Abs_exists); auto.
    assert (multipar G D (a_UAbs rho R (close_tm_wrt_tm x b))
                       (a_UAbs rho R (close_tm_wrt_tm x c)) R0).
    { apply IHmultipar; auto.
    * inversion lc; subst; clear lc.
        constructor; eauto.
        intros x0.
        rewrite -tm_subst_tm_tm_spec.
        apply tm_subst_tm_tm_lc_tm; auto.
        apply Par_lc2 in H; auto.
    * rewrite fv_tm_tm_tm_close_tm_wrt_tm_rec.
      fsetdec.
    * rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto. }
    eapply mp_step; eauto.
Qed.

Lemma multipar_CAbs_exists: forall c (G : context) D (a a': tm) R,
       lc_tm (a_UCAbs a) -> c `notin` fv_co_co_tm a
       -> multipar G D (open_tm_wrt_co a (g_Var_f c)) a' R
       → multipar G D (a_UCAbs a) (a_UCAbs (close_tm_wrt_co c a')) R.
Proof.
  intros c G D a a' R lc e H.
  dependent induction H; eauto 1.
    by rewrite close_tm_wrt_co_open_tm_wrt_co; auto.
  inversion lc; subst.
  apply mp_step with (b:= ( (a_UCAbs (close_tm_wrt_co c b)))); eauto.
  + apply (Par_CAbs (singleton c)); auto.
    intros c1 h0.
    rewrite -co_subst_co_tm_spec.
    rewrite (co_subst_co_tm_intro c a (g_Var_f c1)); auto.
    apply subst4; auto.
  + apply IHmultipar; eauto.
    * constructor; eauto 1.
      intros c1.
      rewrite -co_subst_co_tm_spec.
      apply co_subst_co_tm_lc_tm; auto.
      apply Par_lc2 in H; auto.
    * rewrite fv_co_co_tm_close_tm_wrt_co_rec.
      fsetdec.
    * rewrite open_tm_wrt_co_close_tm_wrt_co; auto.
Qed.

Lemma multipar_open_tm_wrt_co_preservation: forall G D B1 B2 c R, multipar G D (open_tm_wrt_co B1 (g_Var_f c)) B2 R -> exists B', B2 = open_tm_wrt_co B' (g_Var_f c) /\ multipar G D (open_tm_wrt_co B1 (g_Var_f c)) (open_tm_wrt_co B' (g_Var_f c)) R.
Proof.
  intros G D B1 B2 c R H.
  exists (close_tm_wrt_co c B2).
  have:open_tm_wrt_co (close_tm_wrt_co c B2) (g_Var_f c) = B2 by apply open_tm_wrt_co_close_tm_wrt_co.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.

Lemma multipar_open_tm_wrt_tm_preservation: forall G D B1 B2 R x, multipar G D (open_tm_wrt_tm B1 (a_Var_f x)) B2 R -> exists B', B2 = open_tm_wrt_tm B' (a_Var_f x) /\ multipar G D (open_tm_wrt_tm B1 (a_Var_f x)) (open_tm_wrt_tm B' (a_Var_f x)) R.
Proof.
  intros G D B1 B2 R x H.
  exists (close_tm_wrt_tm x B2).
  have:open_tm_wrt_tm (close_tm_wrt_tm x B2) (a_Var_f x) = B2 by apply open_tm_wrt_tm_close_tm_wrt_tm.
  move => h0.
  split; eauto.
  rewrite h0.
  eauto.
Qed.

Lemma context_Par_irrelevance: forall G1 G2 D1 D2 a a' R,
                                             Par G1 D1 a a' R -> Par G2 D2 a a' R.
Proof.
  intros G1 G2 D1 D2 a a' R H.
  induction H; eauto.
Qed.


Lemma multipar_context_independent: forall G1 G2 D A B R,  multipar G1 D A B R -> multipar G2 D A B R.
Proof.
  induction 1; eauto.
  apply (@context_Par_irrelevance _ G2 D D) in H; eauto.
Qed.


(* -------------------- weakening stuff for Par ---------------------- *)

Lemma Par_weaken_available :
  forall G D a b R, Par G D a b R -> forall D', D [<=] D' -> Par G D' a b R.
Proof.
  intros. induction H; eauto 4; try done.
  - econstructor; eauto 2.
Qed.

Lemma Par_respects_atoms:
  forall G D a b R, Par G D a b R -> forall D', D [=] D' -> Par G D' a b R.
Proof.
  intros; induction H.
  all: pre; subst; eauto 5.
  - econstructor; eauto 2.
Qed.

Lemma Par_availability_independence: forall G D1 D2 a b R, Par G D1 a b R -> Par G D2 a b R.
Proof.
  induction 1; eauto.
Qed.


Lemma Par_remove_available:
  forall G D a b R, Par G D a b R -> Par G (AtomSetImpl.inter D (dom G)) a b R.
Proof.
  induction 1; eauto 4; try done.
Qed.

Lemma Par_weakening :
  forall G0 D a b R, Par G0 D a b R ->
  forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) ->  Par (F ++ E ++ G) D a b R.
Proof.
  intros; induction H; pre; subst; try done; eauto 4.
  all: first [Par_pick_fresh c;
       try auto_rew_env; apply_first_hyp; try simpl_env | idtac]; eauto 3.
Qed.
