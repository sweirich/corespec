Require Import FcEtt.imports.
Require Import FcEtt.tactics.

Require Import FcEtt.ett_ott.
Require Import FcEtt.ett_inf.
Require Import FcEtt.ett_inf_cs.
Require Import FcEtt.ett_ind.
Require Import FcEtt.ett_par.

Require Import FcEtt.utils.

Require Import FcEtt.erase_syntax.
Require Import FcEtt.ext_invert.
Require Import FcEtt.fc_unique.

Require Import FcEtt.fc_invert.

Require Import FcEtt.erase.
Require Import FcEtt.congruence.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

    Lemma map_map : forall a1 x G2,
        map erase_sort (map (tm_subst_tm_sort a1 x) G2) =
        map (tm_subst_tm_sort (erase a1) x) (map erase_sort G2).
    Proof.
      intros. induction G2.
      - simpl. auto.
      - simpl. destruct a.
        f_equal. f_equal.
        destruct s. simpl.
        rewrite subst_tm_erase_tm. auto.
        simpl. destruct (subst_tm_erase a1 x) as (_ & _ & _ & h).
        rewrite h. autorewcs. auto.
        auto.
    Qed.


Lemma an_congruence :
  forall G a A, AnnTyping G a A ->
           forall G1 x A1 g a1 a2 D,
             G = [(x, Tm A1)] ++ G1 ->
             AnnTyping G1 a1 A1 ->
             AnnTyping G1 a2 A1 ->
             AnnDefEq G1 D g a1 a2 ->
             exists g', AnnDefEq G1 D g'
                        (tm_subst_tm_tm a1 x a) (tm_subst_tm_tm a2 x a).
Proof.
  intros.
  move: (AnnTyping_erase H1) => EH1.
  move: (AnnDefEq_erase H3 H1) => EH2.
  move: (AnnTyping_erase H) => EH.
  subst G.
  assert (EQ: (erase_context ([(x, Tm A1)] ++ G1))  =
              ([(x, Tm (erase A1))] ++ erase_context G1)).
  { unfold erase_context. rewrite map_app.
    f_equal. }
  rewrite EQ in EH.
  have CTX: Ctx ([(x, Tm (erase A1))] ++ erase_context G1) by eauto.
  have CTX2: Ctx (erase_context G1) by eapply Ctx_strengthen; eauto.
  have ACTX2: AnnCtx G1 by eauto with ctx_wff.
  move: (AnnTyping_regularity H) => HA.
  move: (AnnTyping_erase HA) => EA. simpl in EA. simpl_env in EA.
  have TS: Typing (erase_context G1) a_Star a_Star
    by eauto.
  move: (first congruence _ _ _ EA _ nil _ _ _ _ _ eq_refl EH1 EH2) => CA.
  simpl in CA.
  destruct (fourth annotation_mutual _ _ _ _ _ CA) with (G0 := G1)
    as ( ga & a0 & b0 & A0  & E1 & E2 & E3 & DE1 & ATa0 & ATb0 )
  ; simpl; eauto 2.
  rewrite subst_tm_erase_tm in E1.
  rewrite subst_tm_erase_tm in E2.
  have Ta1: AnnTyping G1
                      (tm_subst_tm_tm a1 x a)
                      (tm_subst_tm_tm a1 x A) by
      eapply (AnnTyping_tm_subst); eauto.
  have Ta2: AnnTyping G1
                      (tm_subst_tm_tm a2 x a)
                      (tm_subst_tm_tm a2 x A) by
  eapply (AnnTyping_tm_subst); eauto.
  have Ta3: AnnTyping G1 (tm_subst_tm_tm a1 x A) a_Star.
  eapply (AnnTyping_regularity); eauto 1.
  have Ta4: AnnTyping G1 (tm_subst_tm_tm a2 x A) a_Star by
  eapply (AnnTyping_regularity); eauto.

  have DE2: exists g, AnnDefEq G1 D g  (tm_subst_tm_tm a1 x A) (tm_subst_tm_tm a2 x A).
  { eexists. eapply An_Trans2 with (a1 := a0).
    eapply An_EraseEq. eauto. eauto. eauto.
    eapply An_EraseEq. eauto. eapply AnnTyping_regularity; eauto. auto.
    eapply An_Refl. eauto.
    eapply An_Trans2 with (a1 := b0). eauto.
    eapply An_EraseEq. eauto. eauto. eauto.
    eapply An_EraseEq. eauto. eapply AnnTyping_regularity; eauto. auto. auto.
    eapply An_Refl. eauto. }
  destruct DE2 as (g1 & DEA1A2).

  clear DE1 ATa0 ATb0 E1 E2 E3 a0 b0 A0 ga.

  move: (first congruence _ _ _ EH _ nil _ _ _ _ _ eq_refl EH1 EH2) => CC.
  destruct (fourth annotation_mutual _ _ _ _ _ CC) with (G0 := G1)
    as ( ga & a0 & b0 & A0  & E1 & E2 & E3 & DE1 & ATa0 & ATb0 )
  ; simpl; eauto 2.
  rewrite subst_tm_erase_tm in E1.
  rewrite subst_tm_erase_tm in E2.
  rewrite subst_tm_erase_tm in E3.

  have DE3 : exists g, AnnDefEq G1 D g (tm_subst_tm_tm a1 x A) A0.
  { eexists. eapply An_EraseEq. eauto. eapply AnnTyping_regularity. eauto. eauto.
    eauto. }
  destruct DE3 as (g2 & DEA1A0).
  have DE4 : exists g, AnnDefEq G1 D g (tm_subst_tm_tm a2 x A) A0.
  { eexists. eapply An_Trans2 with (a1 := tm_subst_tm_tm a1 x A).
    eapply An_Sym; eauto. eauto. }
  destruct DE4 as (g3 & DEA2A0).

  eexists.
  eapply An_Trans2 with (a1 := a0).
  { eapply An_EraseEq; eauto 1.
    eapply AnnDefEq_weaken_available; eauto 2. }
  eapply An_Trans2 with (a1 := b0). eauto.
  { eapply An_EraseEq; eauto 1.
    eapply AnnDefEq_weaken_available; eauto 2.
    eapply An_Sym; eauto 2.
    eapply AnnTyping_regularity; eauto.
    eauto.
  }
  Unshelve.
Qed.
