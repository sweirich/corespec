Require Import FcEtt.tactics.
Require Import FcEtt.utils.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.
Require Export FcEtt.labels.
Require Export FcEtt.grade_sig.
Require Import FcEtt.toplevel.
Require Import FcEtt.ext_wf.

Open Scope grade_scope.


Lemma Typing_leq_C :
    (forall G psi b A, Typing G psi b A -> psi <= q_C) /\
    (forall G0 psi phi (H : PropWff G0 psi phi), psi <= q_C) /\
     (forall G0 psi p1 p2 (H : Iso G0 psi p1 p2), psi <= q_C) /\
     (forall G0 psi phi (H : DefEq G0 psi phi), psi <= q_C) /\
      (forall G0 (H : Ctx G0), True) /\
    (forall G0 psi psi0 A B T (H : CDefEq G0 psi psi0 A B T), psi <= q_C).
Proof. 
  apply typing_wff_iso_defeq_mutual; intros; subst; simpl; simpl_env; auto.
  all : try solve [pick fresh x; repeat spec x; auto].
  - hauto lq: on db: lattice_props use: leq_join_r.
Qed.

Lemma join_ctx_r_ctx_sub : forall W q, uniq W ->  ctx_sub W (join_ctx_r q W).
intros. induction W; simpl; eauto. destruct a. destruct p.
destruct_uniq. destruct s; econstructor; eauto.
eapply leq_join_l. unfold join_ctx_r.  auto.
eapply leq_join_l. unfold join_ctx_r.  auto.
Qed.

Lemma Ctx_join_ctx_r_ctx_sub : forall G q, Ctx G ->  ctx_sub G (join_ctx_r q G).
Proof.
  sfirstorder use:join_ctx_r_ctx_sub, Ctx_uniq.
Qed.

(* Lemma Ctx_change_label_front : *)
(*   forall x psi B G, Ctx ([(x, (psi, B))] ++ G) -> forall psi', Ctx ([(x, (psi', B))] ++ G). *)
(* Proof. *)
(*   move => x psi B G H. *)
(*   dependent induction H; eauto. *)
(* Qed. *)

(* Lemma Ctx_change_label_middle : *)
(*   forall F x psi B G, Ctx (F ++ [(x, (psi, B))] ++ G) -> forall psi', Ctx (F ++ [(x, (psi', B))] ++ G). *)
(* Proof. *)
(*   induction F; eauto using Ctx_change_label_front. *)
(*   move => x psi B G HCtx psi'. *)
(*   inversion HCtx; subst. *)
(*   - simpl. *)
(*     constructor. *)

(* Qed. *)

Lemma Typing_narrowing : forall {G0 psi a A}, Typing G0 psi a A -> forall {G1}, ctx_sub G1 G0 -> Typing G1 psi a A.
Proof.
  hauto l:on use:ctx_wff_narrow_mutual.
Qed.

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma Typing_pumping_middle :
  (forall G psi b A (H : Typing G psi b A),
     forall x B psi0 E F psi1, 
         G = E ++ [(x, (psi0, B))] ++  F -> 
         psi1 <= psi -> 
         Typing (E ++ [(x, (psi0 * psi1, B))] ++ F) psi b A) /\
  (forall G psi phi (H : PropWff G psi phi),
      forall x B psi0 E F psi1, 
         G = E ++ [(x, (psi0, B))] ++  F -> 
         psi1 <= psi -> 
         PropWff (E ++ [(x, (psi0 * psi1, B))] ++ F) psi phi) /\
  (forall G psi p1 p2 (H : Iso G psi p1 p2),
      forall x B psi0 E F psi1, 
         G = E ++ [(x, (psi0, B))] ++  F -> 
         psi1 <= psi -> 
         Iso (E ++ [(x, (psi0 * psi1, B))] ++ F) psi p1 p2) /\
  (forall G psi phi (H : DefEq G psi phi),
      forall x B psi0 E F psi1, 
         G = E ++ [(x, (psi0, B))] ++  F -> 
         psi1 <= psi -> 
         DefEq (E ++ [(x, (psi0 * psi1, B))] ++ F) psi phi) /\
  (forall G (H : Ctx G),
    forall x B psi0 E F psi1,
      G = E ++ [(x, (psi0, B))] ++  F ->
      psi1 <= q_C ->
      Ctx (E ++ [(x, (psi0 * psi1, B))] ++ F)) /\

  (forall G psi psi2 a b T (H : CDefEq G psi psi2 a b T), 
      forall x B psi0 E F psi1, 
         G = E ++ [(x, (psi0, B))] ++  F -> 
         psi1 <= psi -> 
         CDefEq (E ++ [(x, (psi0 * psi1, B))] ++ F) psi psi2 a b T).
Proof.
  Ltac reassoc_env := match goal with
                       |  |- context[?A ++ ?B ++ ?C ++ ?D] => rewrite_env ((A ++ B) ++ C ++ D)
                      end.

  ext_induction CON; intros; subst; eauto 3.
  all : try solve [eapply CON; eauto 3 using q_leb_trans].
  (* tactic below should solve : Pi, CPi, PiCong, CPiCOng *)
  all : try solve [pick fresh y and apply CON; auto;
                   destruct_notin;
                   repeat spec y;
                   reassoc_env;
                   auto].
  (* TODO: pull out abs in the same way *)
  - apply binds_cases in b; auto.
    move : b => [h0 | [h1 | h2]]; split_hyp.
    + apply E_Var with (psi0 := psi0);
      sfirstorder use:q_leb_trans.
    + inversion H2; subst.
      apply E_Var with (psi0 := psi1 * psi2);
        sfirstorder use:join_lub, q_leb_trans.
    + apply E_Var with (psi0 := psi0); sfirstorder use:q_leb_trans.
  (* Abs *)
  - pick fresh y and apply CON.
    auto;
    destruct_notin;
      repeat spec y.
    + reassoc_env.
      auto.
    + have LEQ: psi2 <= q_C.
      transitivity psi; auto.
      pick fresh y.
      spec y.
      sfirstorder use:Typing_leq_C.
      simpl_env.
      rewrite meet_mult; auto.
      apply H0; auto.
      hauto l:on use:map_app.
  (* App *)
  - have h0 : psi <= q_C by pick fresh x0; spec x0; sfirstorder use: Typing_leq_C.
    eapply CON; eauto.
    eapply H0; eauto.
    transitivity psi; eauto.
    apply leq_join_r.
  (* AppIrrel *)
  - have h0 : psi <= q_C.
    pick fresh x0; spec x0.
    sfirstorder use: Typing_leq_C.
    have LEQ: psi2 <= q_C.
    transitivity psi; auto.
    eapply CON; eauto.
    simpl_env.
    rewrite meet_mult; auto.
    apply H0; 
      simpl_env; auto.
  (* Conv *)
  - have h0 : psi <= q_C.
    pick fresh x0; spec x0.
    sfirstorder use: Typing_leq_C.
    have LEQ: psi1 <= q_C.
    transitivity psi; auto.
    eapply CON; simpl_env; try rewrite meet_mult; eauto 3.
    apply H0; simpl_env; eauto.
    apply H1; simpl_env; eauto.
  (* CAbs *)
  - pick fresh y and apply CON.
    auto;
    destruct_notin;
      repeat spec y.
    + reassoc_env.
      auto.
    + have LEQ: psi2 <= q_C.
      transitivity psi; auto.
      pick fresh y.
      spec y.
      sfirstorder use:Typing_leq_C.
      simpl_env.
      rewrite meet_mult; auto.
      apply H0; auto.
      hauto l:on use:map_app.
  (* CApp *)
  - have h0 : psi <= q_C.
    pick fresh x0; spec x0.
    sfirstorder use: Typing_leq_C.
    have LEQ: psi1 <= q_C.
    transitivity psi; auto.
    eapply CON; eauto 3.
    simpl_env.
    rewrite meet_mult; auto.
    apply H0; simpl_env; auto.
  (* Assn (Var case for DefEq) *)
  - apply binds_cases in b; auto.
    move : b => [h0 | [h1 | h2]]; split_hyp.
    + apply E_Assn with (psi0 := psi0) (c := c); 
      sfirstorder use:q_leb_trans.
    + inversion H2; subst.
      apply E_Assn with (psi0 := psi1 * psi2) (c := x); sfirstorder use:q_leb_trans use:join_lub.
    + apply E_Assn with (psi0 := psi0) (c := c); sfirstorder use:q_leb_trans.
  (* AbsCong *)
  - pick fresh y and apply CON.
    auto;
    destruct_notin;
      repeat spec y.
    + reassoc_env.
      auto.
    + have LEQ: psi2 <= q_C.
      transitivity psi; auto.
      pick fresh y.
      spec y.
      sfirstorder use:q_leb_trans use:Typing_leq_C.
      simpl_env.
      rewrite meet_mult; auto.
      apply H0; auto.
      hauto l:on use:map_app.
  (* CAbsCong *)
  - pick fresh y and apply CON.
    auto;
    destruct_notin;
      repeat spec y.
    + reassoc_env.
      auto.
    + have LEQ: psi1 <= q_C.
      transitivity psi; auto.
      pick fresh y.
      spec y.
      sfirstorder use:q_leb_trans use:Typing_leq_C.
      simpl_env.
      rewrite meet_mult; auto.
      apply H0; auto.
      hauto l:on use:map_app.
  (* CAppCong *)
  - have h0 : psi <= q_C.
    pick fresh x0; spec x0.
    sfirstorder use:q_leb_trans use: Typing_leq_C.
    have LEQ: psi1 <= q_C.
    transitivity psi; auto.
    eapply CON; eauto 3.
    simpl_env.
    rewrite meet_mult; auto.
    apply H0; simpl_env; auto.
  (* CPiSnd *)
  - have h0 : psi <= q_C.
    pick fresh x0; spec x0.
    sfirstorder use:q_leb_trans use: Typing_leq_C.
    have LEQ: psi2 <= q_C.
    transitivity psi; auto.
    eapply CON; eauto 3.
    simpl_env.
    rewrite meet_mult; auto.
    apply H0; auto.
    simpl_env. reflexivity.
    simpl_env;
    rewrite meet_mult; auto.
    apply H1; auto.
    simpl_env. reflexivity.
  (* EqConv *)
  - have h0 : psi <= q_C.
    pick fresh x0; spec x0.
    sfirstorder use:q_leb_trans use: Typing_leq_C.
    have LEQ: psi1 <= q_C.
    transitivity psi; auto.
    eapply CON; simpl_env; try rewrite meet_mult; eauto 3.
    apply H0; simpl_env; eauto.
  - have h0 : psi <= q_C.
    pick fresh x0; spec x0.
    sfirstorder use:q_leb_trans use: Typing_leq_C.
    have LEQ: psi1 <= q_C.
    transitivity psi; auto.
    apply CON with (c := c); simpl_env; try rewrite meet_mult; eauto 3.
    reassoc_env.
    apply H; eauto.
    try rewrite meet_mult; eauto 3.
    apply H0; eauto.
    simpl_env; auto.
  - induction E; scongruence.
  - destruct E.
    + simpl in *; inversion H1; subst; auto.
    + simpl in H1.
      simpl.
      simpl in H.
      inversion H1; subst; auto.
      simpl.
      constructor; eauto 2.
      simpl_env; auto.
      rewrite meet_mult; auto.
      apply H0; auto.
      simpl_env. reflexivity.
  - destruct E.
    + simpl in H1; simpl.
      inversion H1; subst.
      constructor; auto.
    + simpl in H1; simpl.
      inversion H1; subst.
      constructor; auto.
      apply H; auto.
      simpl_env.
      rewrite meet_mult; auto.
      apply H0; auto.
      simpl_env; auto.
  - have h0 : psi0 * psi <= q_C.
    pick fresh x0; spec x0.
    sfirstorder use:q_leb_trans use: Typing_leq_C.
    have h1 : psi <= q_C.
    transitivity (psi0 * psi); auto.
    apply leq_join_r.
    have h3 : psi2 <= psi0 * psi.
    transitivity psi; auto.
    apply leq_join_r.
    move : (H1 x B psi1 E F psi2 ltac:(reflexivity) ltac:(auto)) => h2.
    apply CON; auto.
    hauto l:on use:Typing_Ctx.
  - have h0 : psi2 <= q_C.
    transitivity psi; auto.
    move: (H1 x B (q_C + psi1)
              (meet_ctx_l q_C E)
              (meet_ctx_l q_C F)
              psi2
              ltac:(simpl_env; reflexivity)
                     ltac:(sfirstorder use:q_leb_trans)) => h1.
    move: (H0 x B (q_C + psi1)
              (meet_ctx_l q_C E)
              (meet_ctx_l q_C F)
              psi2
              ltac:(simpl_env; reflexivity)
                     ltac:(sfirstorder use:q_leb_trans)) => h2.
    apply CON; eauto 2.
    all: simpl_env; auto; rewrite meet_mult; auto.
Qed.
