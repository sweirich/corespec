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


Lemma Typing_pumping_middle :
  (forall G psi b A (H : Typing G psi b A),
     forall x B psi0 E F, 
         G = E ++ [(x, (psi0, B))] ++  F -> 
         psi0 <= psi -> 
         Typing (E ++ [(x, (psi0 * psi, B))] ++ F) psi b A) /\
  (forall G psi phi (H : PropWff G psi phi),
      forall x B psi0 E F, 
         G = E ++ [(x, (psi0, B))] ++  F -> 
         psi0 <= psi -> 
         PropWff (E ++ [(x, (psi0 * psi, B))] ++ F) psi phi) /\
  (forall G psi p1 p2 (H : Iso G psi p1 p2),
      forall x B psi0 E F, 
         G = E ++ [(x, (psi0, B))] ++  F -> 
         psi0 <= psi -> 
         Iso (E ++ [(x, (psi0 * psi, B))] ++ F) psi p1 p2) /\
  (forall G psi phi (H : DefEq G psi phi),
      forall x B psi0 E F, 
         G = E ++ [(x, (psi0, B))] ++  F -> 
         psi0 <= psi -> 
         DefEq (E ++ [(x, (psi0 * psi, B))] ++ F) psi phi) /\
    (* should be proven separately; Ctx G, G' = G except labels -> Ctx G' *)
  (forall G (H : Ctx G),
      forall x B psi psi' E F,
         G = E ++ [(x, (psi, B))] ++  F ->
         Ctx (E ++ [(x, (psi', B))] ++ F)) /\
  (forall G psi psi0 a b T (H : CDefEq G psi psi0 a b T), 
      forall x B psi0 E F, 
         G = E ++ [(x, (psi0, B))] ++  F -> 
         psi0 <= psi -> 
         CDefEq (E ++ [(x, (psi0 * psi, B))] ++ F) psi psi0 a b T).
Proof.
  apply typing_wff_iso_defeq_mutual; intros; subst; eauto 3.
  - apply binds_cases in b; auto.
    move : b => [h0 | [h1 | h2]]; split_hyp.
    + apply E_Var with (psi0 := psi0); 
      sfirstorder.
    + inversion H2; subst.
      apply E_Var with (psi0 := psi1 * psi); auto.
      sfirstorder.
      have h0: psi1 * psi = psi.
      apply join_leq; auto.
      rewrite h0.
      apply q_leb_refl.
    + apply E_Var with (psi0 := psi0); sfirstorder.
  - 
    
