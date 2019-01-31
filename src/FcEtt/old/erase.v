Require Import FcEtt.sigs.


Require Import FcEtt.utils.
Require Import FcEtt.ett_inf_cs.
Require Import FcEtt.ett_ind.
Require Import FcEtt.imports.
Require Import FcEtt.tactics.
Require Import FcEtt.erase_syntax.
Require Import FcEtt.ext_red.  (* weakening for available cos *)
Require Import FcEtt.fc_invert FcEtt.fc_unique.
Require Import FcEtt.ett_par.
Require Import FcEtt.toplevel.
Require Import FcEtt.fc_context_fv.


Module erase (wf : fc_wf_sig) (weak : fc_weak_sig) (subst : fc_subst_sig)
             (e_invert : ext_invert_sig).

Include e_invert.

Module e_red := ext_red e_invert.
Import e_red.

Import wf weak subst.

Module invert := fc_invert wf weak subst.
Module unique := fc_unique wf subst.
Import invert unique.

Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".



Hint Constructors Typing PropWff Iso DefEq Ctx.

Ltac dispatch_rho  :=
  match goal with
  |  H11 : ∀ x : atom,
      ¬ x `in` ?L0 →
             RhoCheck ?rho x (erase_tm (open_tm_wrt_tm ?b1 (a_Var_f x)))
             |-
             ∀ x : atom,
               ¬ x `in` ?LL → RhoCheck ?rho x (open_tm_wrt_tm (erase_tm ?b1) (a_Var_f x))
           =>
   let Fr := fresh in
   let r' := fresh in
   intros x; intros;
   assert (FrL0 : x `notin` L0); eauto;
   move: (H11 x FrL0) => r';
   autorewcshyp r';
   rewrite -open_tm_erase_tm in r'; eapply r'
end.


(* ------------------------------------------ *)


Lemma erase_mutual :
  (forall G a A, AnnTyping G a A ->
          Typing (erase_context G) (erase a) (erase A)) /\
  (forall G phi, AnnPropWff G phi ->
          PropWff (erase_context G) (erase phi)) /\
  (forall G D g p1 p2, AnnIso G D g p1 p2 ->
          Iso (erase_context G) D
              (erase_constraint p1) (erase_constraint p2)) /\
  (forall G D g a b,
      AnnDefEq G D g a b ->
      forall A, AnnTyping G a A ->
             DefEq (erase_context G) D (erase a) (erase b) (erase A)) /\
  (forall G, AnnCtx G -> Ctx (erase_context G) /\
    forall c t, binds c t G -> binds c (erase_sort t) (erase_context G)).
Proof.
  eapply ann_typing_wff_iso_defeq_mutual.
  all:  intros; split_hyp; try solve [simpl; split_hyp; auto; eauto 2].
  - eapply E_Var; auto.
    rewrite -[Tm (erase _)]/(erase_sort (Tm _)) /erase_context.
    apply binds_map_2.
    auto.
  - simpl. pick fresh x and apply E_Pi; auto.
    replace (a_Var_f x) with (erase (a_Var_f x)); auto.
    rewrite open_tm_erase_tm.
    rewrite_env (erase_context ((x ~ Tm A) ++ G)).
    eapply H. auto.
  - simpl.
    pick fresh x and apply E_Abs; auto.
    assert (FrL : x `notin` L). auto.
    pose (J := H0 x FrL).
    rewrite <- open_tm_erase_tm in J.
    rewrite <- open_tm_erase_tm in J.
    unfold erase_context in J.
    rewrite map_app in J.
    simpl in J. auto.
    assert (FrL : x `notin` L). auto.
    move: (r x FrL) => r'.
    autorewcshyp r'.
    rewrite -open_tm_erase_tm in r'.
    eapply r'.
  - rewrite -open_tm_erase_tm.
    simpl in H. simpl.
    destruct rho; simpl; eauto.
  - (* cast *)
    simpl. autorewcs.
    eapply E_Conv; eauto 1.
    rewrite <- erase_dom.
    pose KA := AnnTyping_regularity a0. clearbody KA.
    eapply (H0 a_Star).
    auto.
  - simpl. pick fresh x and apply E_CPi; eauto.
    autorewcs.
    rewrite (open_co_erase_tm2 (g_Var_f x)).
    rewrite_env (erase_context ((x ~ Co phi) ++ G)).
    eauto.
  - pick fresh x and apply E_CAbs; auto.
    assert (FrL : x `notin` L). auto.
    pose (J := H0 x FrL).
    rewrite (open_co_erase_tm2 (g_Var_f x)).
    rewrite (open_co_erase_tm2 (g_Var_f x)).
    auto.
  - rewrite -(open_co_erase_tm2 _ _ g_Triv) /=.
    pose K := AnnTyping_regularity a0. clearbody K. inversion K. inversion H4. subst.
    eapply E_CApp. simpl in H. eauto.
    rewrite <- erase_dom.
    eapply H0; eauto.
  - simpl. eapply E_Fam; eauto.
    unfold toplevel.
    unfold erase_sig.
    replace (Ax (erase_tm a) (erase_tm A)) with (erase_csort (Ax a A)); auto.
  - simpl.
    econstructor; autorewcs.
    + eauto.
    + autorewcshyp e.
        by rewrite e.
    + eapply Typing_regularity; eauto 1.
  - assert (Ctx (erase_context G)). eauto.
    simpl in *. inversion a1. inversion a2. subst.
    eapply E_PropCong. eapply H; eauto. rewrite H10. eapply H0; eauto.
  - destruct (AnnDefEq_regularity a) as [S1 [S2 [g' [AT1 [AT2 _]]]]].
    inversion AT1. inversion AT2. subst.
    destruct phi1. destruct phi2. simpl in *.
    eapply E_CPiFst. eapply (H a_Star); eauto.
  - eapply sym_iso. auto.
  - simpl. rewrite e. rewrite e0.
    inversion a0.
    inversion H0. subst.
    simpl in *. eapply E_IsoConv; eauto 1.
    eapply (H a_Star).  eapply AnnTyping_regularity. eauto.
    inversion H1. subst.
    eapply E_Wff; eauto 1. eapply E_Conv; eauto 1.
    eapply E_Sym. eapply DefEq_weaken_available. eapply (H a_Star). eauto 1.
    eapply AnnTyping_regularity. eauto.
     eapply E_Conv; eauto 1.
    eapply E_Sym. eapply DefEq_weaken_available. eapply (H a_Star). eauto 1.
    eapply AnnTyping_regularity. eauto.
  - pose K:= (binds_to_AnnPropWff _ _ _ _ a0 b0). clearbody K. inversion K. subst.
    resolve_unique_nosubst.
    pose M := H1 c (Co (Eq a b A0)) b0.
    eapply E_Assn; eauto.
  - simpl.
    resolve_unique_nosubst.
    subst.
    eapply E_Refl; auto.
  - resolve_unique_nosubst.
    assert (K :Ctx (erase_context G)) . eauto.
    pose R1 := AnnTyping_regularity a0.
    pose R2 := AnnTyping_regularity a1.
    simpl. rewrite -e.
    eapply E_Refl; eauto.
  - eapply E_Sym.
    resolve_unique_nosubst.
    pose R1 := AnnTyping_regularity a0.
    pose R2 := AnnTyping_regularity a1.
    pose K1 := H1 a_Star R1. clearbody K1. simpl in K1.
    pose K2 := H2 B a0. clearbody K2.
    eapply DefEq_conv. eauto.
  rewrite <- erase_dom. auto.
  - (* trans *)
    destruct (AnnDefEq_regularity a0) as [S1 [S2 [g4 [T1 [T2 DE]]]]].
    destruct (AnnDefEq_regularity a2) as [S1' [S2' [g4' [T1' [T2' DE']]]]].
    resolve_unique_nosubst.
    resolve_unique_nosubst.
    resolve_unique_nosubst.
    resolve_unique_nosubst.
    eapply E_Trans. eauto.
    eapply DefEq_conv. eauto.
    rewrite <- erase_dom.
    eapply E_Sym. eapply (H3 a_Star).
    eapply AnnTyping_regularity. eauto.
  - simpl.
    assert (Ctx (erase_context G)). eauto.
    resolve_unique_nosubst.
    eapply E_Beta. auto. auto. rewrite e. eauto. eauto.
  - (* pi-cong*)
    assert (A = a_Star). eapply AnnTyping_unique; eauto. subst.
    simpl.
    inversion a1. subst.
    eapply (E_PiCong (L \u L0)); try solve [simpl in *; eauto 2].
    + eapply (H a_Star). auto.
    + intros x Fr. assert (FrL : x `notin` L). auto.
      pose K := H0 x FrL a_Star. clearbody K. clear H0.
      rewrite -open_tm_erase_tm in K.
      simpl.
      simpl in K.
      have: a_Var_f x  = erase (a_Var_f x) by done.
      move=> ->.
      rewrite (open_tm_erase_tm B3) e.
      rewrite -(open_tm_erase_tm B2). simpl.
      have: a_Var_f x  = erase (a_Var_f x) by done.
      move=> ->.
      rewrite (open_tm_erase_tm B2).
      simpl.
      eapply K.
      eapply H8. auto. auto.
   + simpl in H1. eapply invert_a_Pi. eauto.
  - simpl.
    inversion H4. subst. simpl.
    eapply (E_AbsCong (L \u L0)) ; auto.
    intros x Fr.
    assert (FrL : x `notin` L). auto. assert (FrL0 : x `notin` L0). auto.
    assert (EQ: (erase (open_tm_wrt_tm b3 (a_Var_f x))) =
                (erase (open_tm_wrt_tm b2 (a_Var_f x)))).
       rewrite e.
       rewrite <- open_tm_erase_tm.
       rewrite <- open_tm_erase_tm.
       simpl. auto. auto.
    replace (a_Var_f x) with (erase (a_Var_f x)).
    rewrite open_tm_erase_tm.
    rewrite open_tm_erase_tm.
    rewrite open_tm_erase_tm.
    rewrite EQ.
    eapply (H0 x FrL (open_tm_wrt_tm B0 (a_Var_f x))).
    eapply H11; simpl; auto.
    simpl. auto.
    dispatch_rho.
    dispatch_rho.
  - simpl in *.
    resolve_unique_nosubst.
    destruct rho.
    + inversion a3. subst.
    rewrite <- open_tm_erase_tm.
    eapply E_AppCong.
    eapply (H (a_Pi Rel A0 B0)). eauto.
    eapply H0. auto.
    + inversion a3. subst.
      rewrite <- open_tm_erase_tm.
      move: (H _ H9) => h0.
      move: (H0 _ H10) => h1.
      move: (DefEq_regularity h1) => p1.
      inversion p1.
      eapply E_IAppCong; eauto.
  - simpl in *.

    destruct (AnnDefEq_regularity a) as [S1 [S2 [g' [TA1 [TA2 _]]]]].
    inversion TA1. subst.
    resolve_unique_nosubst.
    inversion TA2. subst.
    simpl.
    eapply E_PiFst. eapply (H a_Star). eauto.
  - rewrite <- open_tm_erase_tm.
    rewrite <- open_tm_erase_tm.
    simpl in *.
    destruct (AnnDefEq_regularity a) as [S1 [S2 [g' [TA1 [TA2 _]]]]].
    inversion TA1.
    assert (AnnTyping G (open_tm_wrt_tm B1 a1) a_Star).
    { pick fresh y.
      rewrite (tm_subst_tm_tm_intro y).
      replace a_Star with (tm_subst_tm_tm a1 y a_Star).
      eapply AnnTyping_tm_subst; auto.
      simpl. auto. auto. }
    resolve_unique_nosubst.
    eapply E_PiSnd; eauto 1.
    eapply (H a_Star). eauto.
    eapply (H0 A1). eauto.
  - (* CPiCong *)
    simpl.
    assert (a_Star = A). eapply (AnnTyping_unique a1). eauto. subst. clear H3.
    inversion a1.
    inversion a2. subst.
    eapply (E_CPiCong (L \u dom G \u L0 \u L1)); try solve [simpl in *; eauto 2].
    + intros c Fr. assert (FrL : c `notin` L). auto.
      pose K := a0 c FrL. clearbody K.
      rewrite (open_co_erase_tm2 (g_Var_f c)).
      rewrite (open_co_erase_tm2 g_Triv).
      assert (EQ: (erase (open_tm_wrt_co B3 (g_Var_f c))) =
                  (erase (open_tm_wrt_co B2 (g_Var_f c)))).
      rewrite e.
      rewrite <- open_co_erase_tm.
      rewrite <- open_co_erase_tm. auto. auto.
      rewrite <- (open_co_erase_tm2 g_Triv B3 (g_Var_f c)).
      rewrite (open_co_erase_tm2 (g_Var_f c)).
      rewrite EQ.
      eapply (H0 c FrL a_Star); auto.
    + simpl in H1. eapply invert_a_CPi. eauto.
  - simpl.
    inversion H5. subst.
    simpl.
    eapply (E_CAbsCong (L \u dom G \u L0)).
    + intros c Fr. assert (FrL : c `notin` L). auto.
      pose K := a0 c FrL. clearbody K.
      rewrite (open_co_erase_tm2 (g_Var_f c)).
      rewrite (open_co_erase_tm2 g_Triv).
      assert (EQ: (erase (open_tm_wrt_co a3 (g_Var_f c))) =
                  (erase (open_tm_wrt_co a2 (g_Var_f c)))).
      rewrite e.
      rewrite <- open_co_erase_tm.
      rewrite <- open_co_erase_tm. auto. auto.
      rewrite <- (open_co_erase_tm2 g_Triv a3 (g_Var_f c)).
      rewrite (open_co_erase_tm2 (g_Var_f c)).
      rewrite EQ.
      rewrite (open_co_erase_tm2 (g_Var_f c) B0).
      eapply (H0 c FrL (open_tm_wrt_co B0 (g_Var_f c))).
      eauto.
    + simpl in H1.
      have CT: Ctx (erase_context G) by eauto 2.
      move: (Typing_regularity H1) => TCPi.
      destruct (invert_a_CPi TCPi) as (_ & _ & P).
      eauto.
  - simpl.

    inversion H5. subst.
    inversion a5. subst.
    resolve_unique_subst.
    resolve_unique_subst.

    inversion H6. subst. clear H6. clear H7. clear H11.
    inversion a6. subst.
    autorewcs.
    rewrite <- (open_co_erase_tm2 _ _ g_Triv).
    apply AnnDefEq_weaken_available in a0.
    apply AnnDefEq_weaken_available in a4.
    resolve_unique_subst.
    resolve_unique_subst.
    pose K := AnnTyping_regularity H9. clearbody K.  inversion K.
    inversion H10. subst.
    pose K1 := AnnTyping_regularity H8. clearbody K1. inversion K1.
    inversion H12. subst.
    eapply E_CAppCong.
    move: (H _ H9) => h0. eapply h0. fold erase_tm.
    eapply DefEq_weaken_available. eauto.
  - simpl in H.
    rewrite <- (@open_co_erase_tm2  _ _ g_Triv).
    rewrite <- (@open_co_erase_tm2  _ _ g_Triv).
    simpl.
    destruct (AnnDefEq_regularity a0) as [S1 [S2 [g [AT1 [AT2 _]]]]].
    inversion AT1. subst.
    inversion H6. subst.
     assert (AnnTyping G (open_tm_wrt_co B1 g2) a_Star).
    { pick fresh y.
      rewrite (co_subst_co_tm_intro y).
      replace a_Star with (co_subst_co_tm g2 y a_Star).
      eapply AnnTyping_co_subst; auto.
      simpl. eauto. simpl. auto. auto. }
    resolve_unique_nosubst.
    eapply E_CPiSnd.
    eapply (H a_Star). auto. rewrite -erase_dom. auto.
    inversion AT2. inversion H7.
    rewrite -erase_dom. auto.
  - destruct (AnnIso_regularity a1) as [W1 W2]. inversion W1.  inversion W2. subst.
    resolve_unique_nosubst.
    eapply E_Cast. eauto. eauto.
  - destruct (AnnIso_regularity a0) as [W1 W2]. inversion W1.  inversion W2. subst.
    move: (AnnTyping_regularity H5) => ?.
    resolve_unique_nosubst. simpl.
    eapply E_IsoSnd. eauto.

  - rewrite <- dom_map with (f:=erase_sort) in n.
    unfold erase_context in *.
    split.
    eapply E_ConsTm; auto.
    intros.
    destruct (@binds_cons_1 _ c x _ (Tm A) G H2) as [[E1 E2] | E3].
    + subst. simpl. eauto.
    + simpl. eapply binds_cons_3. auto.
  - rewrite <- dom_map with (f:=erase_sort) in n.
    unfold erase_context in *.
    split.
    eapply E_ConsCo; auto.
    intros.
    destruct (@binds_cons_1 _ c0 c _ (Co phi) G H2) as [[E1 E2] | E3].
    + subst. simpl. eauto.
    + simpl. eapply binds_cons_3. auto.
Qed.


Definition AnnTyping_erase :
  (forall G a A, AnnTyping G a A ->
            Typing (erase_context G) (erase a) (erase A)) := first erase_mutual.
Definition AnnPropWff_erase :
  (forall G phi, AnnPropWff G phi ->
            PropWff (erase_context G) (erase phi)) := second erase_mutual.
Definition AnnIso_erase :
  (forall G D g p1 p2, AnnIso G D g p1 p2 ->
          Iso (erase_context G) D
              (erase_constraint p1) (erase_constraint p2)) := third erase_mutual.
Definition AnnDefEq_erase :
  (forall G D g a b,
      AnnDefEq G D g a b ->
      forall A, AnnTyping G a A ->
           DefEq (erase_context G) D (erase a) (erase b) (erase A)) := fourth erase_mutual.
Definition AnnCtx_erase :
  (forall G, AnnCtx G -> Ctx (erase_context G) /\
    forall c t, binds c t G -> binds c (erase_sort t) (erase_context G)) := fifth erase_mutual.



Lemma erasure_a_Star :
  forall G a A, AnnTyping G a A -> erase A = a_Star ->
           exists a', erase a = erase a' /\ AnnTyping G a' a_Star.
Proof.
  intros G a A H H0.
  remember (g_Refl2 A a_Star (g_Refl a_Star)) as g.
  pose K := AnnTyping_regularity H.
  have L: AnnCtx G by eauto with ctx_wff.
  assert (AnnDefEq G (dom G) g A a_Star).
  { rewrite Heqg. eauto. }
  assert (AnnTyping G a_Star a_Star). eauto.
  exists (a_Conv a g). repeat split. eauto.
Qed.

Lemma erasure_cvt :
    forall G a A, AnnTyping G a A -> forall B, erase A = erase B -> AnnTyping G B a_Star ->
                                    exists a', erase a = erase a' /\ AnnTyping G a' B.
  Proof.
    intros G a A H B e TB.
    pose K := AnnTyping_regularity H. clearbody K.
    remember (g_Refl2 A B (g_Refl a_Star)) as g.
    assert (AnnDefEq G (dom G) g A B).
    { rewrite Heqg. eapply An_EraseEq. eauto. eauto. eauto. eapply An_Refl. eapply An_Star.
      eauto with ctx_wff. }
    remember (a_Conv a (g_Refl2 A B (g_Refl a_Star))) as a0'.
    assert (ATA' : AnnTyping G a0' B).
    { rewrite Heqa0'. rewrite <- Heqg. eapply An_Conv. eauto. eauto. eauto. }
    exists (a_Conv a g). eauto.
  Qed.


Lemma AnnDefEq_invertb : forall G D g a b, AnnDefEq G D g a b ->
  exists A b' g, AnnTyping G a A /\ AnnTyping G b' A /\ erase b' = erase b /\ AnnDefEq G D g b b'.
  Proof.
    intros G D g a b DE.
    destruct (AnnDefEq_regularity DE) as [SA [SB [g4 [AT0' [ATB0' SAB]]]]].
    exists SA. eexists. eexists.
    assert (AnnTyping G (a_Conv b (g_Sym g4)) SA).
    {     eapply An_Conv. eapply ATB0'.
          eapply An_Sym.
          eapply AnnTyping_regularity. eauto.
          eapply AnnTyping_regularity. eauto.
          eapply An_Refl. eapply An_Star.
          eauto with ctx_wff. eauto.
          eapply AnnTyping_regularity. eauto.
    }
    split. auto. split. eauto.
    split. simpl. auto.
    eapply An_EraseEq. eauto. eauto. simpl. eauto.
    eapply An_Sym.
    eapply AnnTyping_regularity. eauto.
    eapply AnnTyping_regularity. eauto.
    eapply An_Refl. eapply An_Star.
    eauto with ctx_wff. eauto.
  Qed.


  (*  ----------------------------------------------------------- *)



Lemma erasure_AnnDefEq : forall G D g A'' B'' S A' B',
      AnnDefEq G D g A'' B'' ->
      AnnTyping G A'' S -> erase S = a_Star ->
      erase A'' = erase A' -> erase B'' = erase B' ->
      AnnTyping G A' a_Star -> AnnTyping G B' a_Star ->
      exists g', AnnDefEq G D g' A' B'.
Proof.
  intros G D g A'' B'' S A' B' H H0 H1 H2 H3 H4 H5.
  destruct (AnnDefEq_invertb H) as (S' & b'' & g' & TA'' & Tb' & Eb' & DEB).
  resolve_unique_nosubst.
  move :(AnnTyping_regularity H0) => R0.
  move :(AnnTyping_regularity Tb') => R1.
  have CTX : AnnCtx G by eauto with ctx_wff.
  assert (TEMP : exists g, AnnDefEq G D g A' A'').
  { eexists.
    eapply An_EraseEq. eauto. eauto. eauto.
    eapply An_EraseEq. eapply An_Star. auto. eauto. eauto.
    eapply An_Refl. eauto. }
  destruct TEMP as (gA & DEA).
  assert (TEMP : exists g, AnnDefEq G D g b'' B').
  { eexists.
    eapply An_EraseEq. eauto. eauto. autorewcs. congruence.
    eapply An_EraseEq. eauto. eauto. eauto.
    eapply An_Refl. eauto. }
  destruct TEMP as (gB & DEB2).
  destruct (An_Trans' DEA H) as [gX TR1].
  destruct (An_Trans' TR1 DEB) as [gX2 TR2].
  destruct (An_Trans' TR2 DEB2) as [gX3 TR3].
  exists gX3. exact TR3.
Qed.


Lemma AnnDefEq_invert_a_Star : forall G0 D g1 A1' A2' S,
      AnnDefEq G0 D g1 A1' A2' ->
      AnnTyping G0 A1' S ->
      erase S = a_Star ->
      exists A1'', exists A2'', exists g, erase A1'' = erase A1'
                       /\ erase A2'' = erase A2'
                       /\ AnnDefEq G0 D g A1'' A2''
                       /\ AnnTyping G0 A1'' a_Star
                       /\ AnnTyping G0 A2'' a_Star.
  Proof.
    intros G0 D g1 A1' A2' S DE T EA3.
  destruct (erasure_a_Star T EA3) as (A1'' & EA1'' & TA1').
  assert (exists g, AnnDefEq G0 D g A1'' A1').
  { eexists. eapply An_EraseEq with (A := a_Star); eauto 1.
    assert (AnnCtx G0). eauto with ctx_wff.
    eapply An_EraseEq with (A := a_Star). eauto.
    eapply AnnTyping_regularity; eauto 1.
    eauto. eapply An_Refl.  eauto.
  }

  destruct H as [g2 DE1].
  destruct (An_Trans' DE1 DE) as [g3 DE2].
  destruct (AnnDefEq_invertb DE2) as (A1''' & A2'' & g4 & ? & T2 & E1 & DE3).
  resolve_unique_nosubst.
  destruct (An_Trans' DE2 DE3) as [g5 DE4].
  exists A1'', A2'', g5.
  repeat split; eauto.
  Qed.



  (*  ----------------------------------------------------------- *)

(* TODO: Would there be a good way to split this proof into smaller parts? *)
Lemma annotation_mutual :
  (forall G a A, Typing G a A ->
     forall G0, erase_context G0 = G -> AnnCtx G0 ->
     exists a0 A0,
         (erase a0) = a /\
         (erase A0) = A /\
         AnnTyping G0 a0 A0) /\
  (forall G phi, PropWff G phi ->
     forall G0, erase_context G0 = G -> AnnCtx G0 ->
     exists phi0,
          erase_constraint phi0 = phi /\
          AnnPropWff G0 phi0) /\
  (forall G D p1 p2, Iso G D p1 p2 ->
     forall G0, erase_context G0 = G -> AnnCtx G0 ->
     exists g0 p1' p2',
       (erase_constraint p1') = p1 /\
       (erase_constraint p2') = p2 /\
       AnnIso G0 D g0 p1' p2') /\
  (forall G D a b A, DefEq G D a b A ->
     forall G0, erase_context G0 = G -> AnnCtx G0 ->
     exists g a0 b0 A0,
       (erase a0) = a /\
       (erase b0) = b /\
       (erase A0) = A /\
       AnnDefEq G0 D g a0 b0 /\ AnnTyping G0 a0 A0 /\ AnnTyping G0 b0 A0) /\
  (forall G, Ctx G -> True).
Proof.
  eapply typing_wff_iso_defeq_mutual; intros; auto.
- exists a_Star. exists a_Star.
  repeat split. auto.
- rename H0 into EQ.
  unfold erase_context in EQ.
  rewrite <- EQ in b.
  apply binds_map_3 in b.
  destruct b as [s' [EQ2 b]].
  destruct s'; simpl in EQ2; inversion EQ2.
  exists (a_Var_f x).
  exists A0.
  unfold erase_context.
  simpl. split; auto.
- (* E_Pi *)
  clear t. clear t0.
  pick fresh x.
  assert (FrL : x `notin` L). auto.
  destruct (H0 G0 H1 H2) as [A0 [S0 [EQ1 [EQ2 AT]]]]. clear H0.
  destruct (erasure_a_Star AT EQ2) as [A0' [EQ3 AS]].
  assert (EQA : erase A0' = A). rewrite <- EQ3. auto.
  assert (AN: AnnCtx ((x ~ Tm A0') ++ G0)). eauto with ctx_wff.
  assert (E : erase_context ([(x, Tm A0')] ++ G0) = [(x, Tm A)] ++ G).
  { unfold erase_context. simpl in *.
    unfold erase_context in H1. congruence. }
  destruct (H x FrL _ E AN) as [B0 [S [E2 [E3 AT2]]]]. clear H. clear E. clear AN.
  destruct (erasure_a_Star AT2 E3) as [B0' [E4 AT4]].
  exists (a_Pi rho A0' (close_tm_wrt_tm x B0')).
  exists a_Star.
  repeat split.
  { simpl.  f_equal; auto. autorewcs.
    rewrite <- (close_tm_erase_tm x B0').
    rewrite <- E4. rewrite E2. simpl.
    rewrite close_tm_wrt_tm_open_tm_wrt_tm; auto. }
  { eapply An_Pi_exists with (x:=x); eauto.
    autorewrite with lngen. fsetdec.
    rewrite open_tm_wrt_tm_close_tm_wrt_tm.
    eauto. }
- (* E_Abs *)
  destruct (H0 G0 H1 H2) as [A0 [s0 [E1 [E2 AT]]]]. clear H0.
  destruct (erasure_a_Star AT E2) as [A0' [EQ3 AS]].
  assert (EQA : erase A0' = A). rewrite <- EQ3. auto.
  pick fresh x. assert (FrL : x `notin` L). auto.
  assert (AN: AnnCtx ((x ~ Tm A0') ++ G0)). eauto with ctx_wff.
  assert (E : erase_context ([(x, Tm A0')] ++ G0) = [(x, Tm A)] ++ G).
     rewrite <- H1. unfold erase_context. simpl in *. congruence.
  destruct (H x FrL _ E AN) as [b0 [B0 [E3 [E4 AT_2]]]]. clear H. clear E.
  exists (a_Abs rho A0' (close_tm_wrt_tm x b0)).
  exists (a_Pi rho A0' (close_tm_wrt_tm x B0)).
  split. simpl in *. subst. f_equal.
  (* Little hack because we need a better control of how simpl simplifies erase (and its monomorphic versions) *)
  set (k := close_tm_erase_tm). simpl in k. unfold close_tm_wrt_tm.
  rewrite <- k; auto. rewrite E3.
  (* assert (k' : forall x', close_tm_wrt_tm_rec 0 x x' = close_tm_wrt_tm x x') by done; rewrite_and_clear k'. *)
  rewrite close_tm_wrt_tm_open_tm_wrt_tm; auto.
  split.
  simpl. subst. f_equal. autorewcs. congruence.
  (* FIXME: general solution *)
  (* have: (forall x (t : tm), close_tm x t = close_tm_rec 0 x t) by reflexivity. move=> ->.*)
  rewrite <- close_tm_erase_tm. rewrite E4. simpl.
  (* assert (k' : forall x', close_tm_wrt_tm_rec 0 x x' = close_tm_wrt_tm x x') by done; rewrite_and_clear k'. *)
  rewrite close_tm_wrt_tm_open_tm_wrt_tm; auto.
  apply An_Abs_exists with (x := x); auto.
  apply notin_union_3; auto.
  apply notin_union_3; auto.
  autorewrite with lngen; auto.
  autorewrite with lngen; auto.
  rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.
  rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.
  rewrite open_tm_wrt_tm_close_tm_wrt_tm; auto.
  autorewcs. rewrite E3.
  eapply r; auto.
- (* E_App *)
  destruct (H G0 H1 H2) as [a0 [AB0 [F1 [F2 Ty2]]]]. clear H.
  destruct (H0 G0 H1 H2) as [b0 [A0 [M1 [M2 Ty3]]]]. clear H0.
  assert (K : AnnTyping G0 AB0 a_Star). eapply AnnTyping_regularity; eauto.
  destruct (erase_pi F2 K) as [PA [PB [EAB [EPA [EPB TYB]]]]].
  inversion TYB. subst.
  assert (N : AnnTyping G0 A0 a_Star). eapply AnnTyping_regularity; eauto.
  destruct (erasure_cvt Ty2 EAB) as [a0' [g ATA']]; eauto.
  destruct (erasure_cvt Ty3 (symmetry EPA)) as [b0' [g' ATB']]; eauto.
  exists (a_App a0' Rel b0').
  exists (open_tm_wrt_tm PB b0').
  simpl. rewrite <- open_tm_erase_tm.
  simpl in *.
  repeat split.
  congruence.
  congruence.
  eauto.
- (* E_IApp case *)
  destruct (H G0 H1 H2) as [a0 [AB0 [F1 [F2 Ty2]]]]. clear H.
  destruct (H0 G0 H1 H2) as [b0 [A0 [M1 [M2 Ty3]]]]. clear H0.
  assert (K : AnnTyping G0 AB0 a_Star). eapply AnnTyping_regularity; eauto.
  destruct (erase_pi F2 K) as [PA [PB [EAB [EPA [EPB TYB]]]]].
  inversion TYB. subst.
  assert (N : AnnTyping G0 A0 a_Star). eapply AnnTyping_regularity; eauto.
  destruct (erasure_cvt Ty2 EAB) as [a0' [g ATA']]; eauto.
  destruct (erasure_cvt Ty3 (symmetry EPA)) as [b0' [g' ATB']]; eauto.
  exists (a_App a0' Irrel b0').
  exists (open_tm_wrt_tm PB b0').
  simpl. rewrite <- open_tm_erase_tm.
  simpl in *.
  repeat split.
  congruence.
  congruence.
  eauto.
- (* ex_conv case *)
  destruct (H G0 H2) as [a0 [A0 [E1 [E2 Ty]]]]; auto. clear H.
  destruct (H0 G0 H2 H3) as
      [g [A0' [B0' [S [Ea [Eb [Es [DE [Z Z']]]]]]]]]; auto; clear H0.
  subst.
  replace a_Star with (erase a_Star) in Es; [|simpl;auto].
  destruct (erasure_cvt Z Es) as [A0'' [AS1 AS2]]. eapply An_Star. assumption.
  assert (Ea' : erase A0 = erase A0''). rewrite -AS1. auto.
  destruct (erasure_cvt Ty Ea') as [a'' [Ea0 Ta0]]. eauto.
  destruct (AnnDefEq_invertb DE) as [SA [B0'' [g5 [AT1 [AT2 [Eb SS]]]]]].
  resolve_unique_nosubst.

  destruct (erasure_a_Star AT2 Es) as (B0 & EB0 & TB0).

  pose A0S := AnnTyping_regularity Ty. clearbody A0S.
  rewrite -erase_dom in DE.
  assert (E1 :exists g, AnnDefEq G0 (dom G0) g A0 A0').
  { eexists.
    eapply An_EraseEq. eauto. eauto. eauto.
    eapply An_EraseEq. eauto. eapply AnnTyping_regularity. eauto. eauto.
    eapply An_Refl. eauto.
  }
  destruct E1.
  assert (E2 : exists g, AnnDefEq G0 (dom G0) g A0' A0'').
  { eexists.
    eapply An_EraseEq. eauto. eapply AnnTyping_regularity. eauto.
    eauto.
    eapply An_EraseEq. eapply AnnTyping_regularity. eauto.
    eapply An_Star. eauto.
    eauto.
    eapply An_Refl. eauto.
  }
  destruct E2.
  assert (E3 : exists g, AnnDefEq G0 (dom G0) g A0'' B0'').
  {
    destruct (An_Sym' H0).
    rewrite -erase_dom in SS.
    destruct (An_Trans' DE SS); try eassumption.
    eapply An_Trans' with (a1 := A0'); try eassumption.
  }
  destruct E3 as [g'' EQ].
  assert (E4 : exists g, AnnDefEq G0 (dom G0) g B0'' B0).
  {
    eexists. eapply An_EraseEq. eauto. eauto. eauto.
    eapply An_EraseEq. eapply AnnTyping_regularity. eauto.
    eapply An_Star. eauto. eauto.
    eapply An_Refl; eauto.
  }
  destruct E4 as (gg & EE).
  destruct (An_Trans' EQ EE).
  eexists (a_Conv a'' x1). eexists B0.
  split. eauto. split. congruence.
  eapply An_Conv. eauto. eauto. eauto.
- (* CPi *)
  pick fresh c. assert (FrL : c `notin` L). auto.
  destruct (H0 G0 H1 H2) as [phi0 [EQ1 AT]]. clear H0.
  assert (AN: AnnCtx ((c ~ Co phi0) ++ G0)). eauto with ctx_wff.
  assert (E : erase_context ([(c, Co phi0)] ++ G0) = [(c, Co phi)] ++ G).
  unfold erase_context. simpl. rewrite EQ1.
  unfold erase_context in H1. rewrite H1. auto.
  destruct (H c FrL _ E AN) as [b0 [S0 [E2 [E3 AT2]]]]. clear H.
  clear E. clear AN.
  destruct (erasure_a_Star AT2) as [b0' [EB N1]]; eauto.
  exists (a_CPi phi0 (close_tm_wrt_co c b0')).
  exists a_Star.
  split.
  simpl. f_equal. auto.
  autorewcs.
  rewrite <- close_co_erase_tm.
  rewrite <- EB. rewrite E2. simpl.
  rewrite close_tm_wrt_co_open_tm_wrt_co; auto.
  split. auto.
  eapply An_CPi_exists with (c := c); eauto.
  apply notin_union_3; auto.
  pose K := fv_co_co_tm_close_tm_wrt_co b0' c. clearbody K.
  unfold AtomSetImpl.Equal in K.
  rewrite K. fsetdec.
  rewrite open_tm_wrt_co_close_tm_wrt_co.
  auto.
- (* abs *)
  destruct (H0 G0 H1 H2) as [A0 [E1 AT]]. clear H0. clear t.
  pick fresh x. assert (FrL : x `notin` L). auto.
  assert (AN: AnnCtx ((x ~ Co A0) ++ G0)). eauto with ctx_wff.
  assert (E : erase_context ([(x, Co A0)] ++ G0) = [(x, Co phi)] ++ G).
     rewrite <- H1. unfold erase_context. simpl. rewrite E1. auto.
  destruct (H x FrL _ E AN) as [b0 [B0 [E3 [E4 AT_2]]]]. clear H. clear E.
  exists (a_CAbs A0 (close_tm_wrt_co x b0)).
  exists (a_CPi A0 (close_tm_wrt_co x B0)).
  split. simpl. subst. f_equal. autorewcs.
  rewrite <- close_co_erase_tm; auto. rewrite E3.
  simpl.
  rewrite close_tm_wrt_co_open_tm_wrt_co; auto.
  split.
  simpl. subst. f_equal. autorewcs.
  rewrite <- close_co_erase_tm. rewrite E4.
  simpl.
  rewrite close_tm_wrt_co_open_tm_wrt_co; auto.
  apply An_CAbs_exists with (c := x); auto.
  { apply notin_union_3; auto.
    apply notin_union_3; auto.
    pose K := fv_co_co_tm_close_tm_wrt_co b0 x. clearbody K.
    unfold AtomSetImpl.Equal in K.
    rewrite K. auto.
    pose K := fv_co_co_tm_close_tm_wrt_co B0 x. clearbody K.
    unfold AtomSetImpl.Equal in K.
    rewrite K. auto.
  }
  rewrite open_tm_wrt_co_close_tm_wrt_co; auto.
  rewrite open_tm_wrt_co_close_tm_wrt_co; auto.
- (* CApp *)
  clear d. clear t.
  destruct (H G0 H1 H2) as [a0 [A0 [E1 [E2 Ty]]]]. clear H.
  destruct (H0 G0 H1 H2) as [g [A0' [B0' [Ea' [Eb DE ]]]]]. clear H0.
  destruct DE as [Eb0 [EA [EQ [AT _]]]].
  pose K := AnnTyping_regularity Ty.
  destruct (erase_cpi E2 K) as [phi2 [B2 [E3 [Ep [EB2 AP]]]]].
  destruct phi2.
  simpl in *. inversion Ep. clear Ep.
  subst.
  rename A1 into A2.
  rename a2 into A1.
  rename b0 into B.
  destruct (erasure_cvt Ty) with (B := a_CPi (Eq A1 B A2) B2) as [a0' [TA' EA']]; eauto.
  inversion AP. inversion H4. subst.
  inversion H6. subst.
  assert (K1 : exists g, AnnDefEq G0 (dom G0) g A1 B0'). {
    eapply An_Trans' with (a1 := A0').
    eapply An_EraseEq. eauto. eauto. eauto.
    eapply An_EraseEq. eapply AnnTyping_regularity. eauto.
    eapply AnnTyping_regularity. eauto. eauto.
    eauto.
    rewrite -erase_dom in EQ.
    eapply EQ.
  }
  destruct K1.
  destruct (AnnDefEq_regularity H) as [C1 [C2 [gB [T1 [T2 DE2]]]]].
  resolve_unique_subst.
  destruct (An_Sym' DE2).
  assert (K3 : exists g, AnnDefEq G0 (dom G0) g C2 B0). {
    eapply An_Trans' with (a1 := C1).
    eauto.
    eapply An_EraseEq. eapply AnnTyping_regularity. eauto.
    eapply AnnTyping_regularity. eauto. eauto. eauto.
  }
  destruct K3.
  assert (K4 : exists g, AnnDefEq G0 (dom G0) g B0' B). {
    eexists. eapply An_EraseEq. eapply T2. eapply H11. eauto.
    eauto.
  }
  destruct K4.
  assert (K2 : exists g, AnnDefEq G0 (dom G0) g A1 B). {
    eapply An_Trans' with (a1 := B0').
    eauto. eauto.
  }
  destruct K2 as [g' Y].
  exists (a_CApp a0' g').
  exists (open_tm_wrt_co B2 g').
  subst. simpl.
  rewrite <- open_co_erase_tm.
  rewrite no_co_in_erased_tm.
  repeat split. autorewcs. congruence.
  eauto.
- destruct (H0 nil eq_refl) as (a0 & A0 & E1 & E2 & Ty). auto.
  unfold toplevel in b. unfold erase_sig in b.
  destruct (@binds_map_3 _ _ F (Ax a A) erase_csort an_toplevel b).
  split_hyp. destruct x; inversion H3.
  exists (a_Fam F). exists A1. repeat split; auto.
  eapply An_Fam; eauto.
  eapply AnnTyping_regularity.
  eapply an_toplevel_closed. eauto.
- destruct (H G0 H2 H3) as [a0 [A0 [E1 [E2 Ty]]]]. clear H.
  destruct (H0 G0 H2 H3) as [b0 [A1 [E3 [E4 TyB]]]]. clear H0.
  clear H1.
  subst.
  exists (Eq a0 b0 A0). simpl. split. auto. eauto.
- (* PropCong *)
  clear d. clear d0.
  rename A1 into a0. rename A2 into b0.
  rename B1 into a1. rename B2 into b1.
  destruct (H G0 H1 H2) as [g0 [a0' [b0' [A' [Ea0 [Eb0 [EA0 [DE0 [T0 _]]]]]]]]]. clear H.
  destruct (H0 G0 H1 H2) as [g1 [a1' [b1' [B' [Ea1 [Eb1 [EA1 [DE1 [T1 _]]]]]]]]]. clear H0.
  move :(AnnTyping_regularity T0) => R0.
  move :(AnnTyping_regularity T1) => R1.

  assert (TEMP: exists g, AnnDefEq G0 (dom G0) g A' B').
  { eexists.  eapply An_EraseEq. eauto. eauto.
    autorewcs. congruence.
    eapply An_Refl. eauto. }
  destruct TEMP as (gX & EqA'B').

  destruct (An_Sym' EqA'B') as (gY & EqB'A').
  remember (a_Conv a1' gY) as a1''.
  assert (AnnTyping G0 a1'' A'). rewrite Heqa1''; eapply An_Conv; eassumption.
  assert (erase a1'' = a1). rewrite Heqa1''. simpl. autorewcs. congruence.
  assert (AnnPropWff G0 (Eq a0' a1'' A')). {
    econstructor. eauto. eauto. autorewcs. congruence.
  }

  (* Now need b0'' : A'. get it from a0' ~ b0' *)
  destruct (AnnDefEq_invertb DE0) as [AA0' [b0'' [gb0 [TA0 [TB0 [E DE0']]]]]].
  resolve_unique_nosubst.

  (* Now we need b1'' : A' get it from a1' ~ b1' ?? *)
  assert (TEMP : exists g, AnnDefEq G0 D g a1'' a1'). {
    eexists.
    eapply An_EraseEq. eauto. eauto. autorewcs. congruence. eauto.
  }
  destruct TEMP as (gZ & Eqa1''a1').
  destruct (An_Trans' Eqa1''a1' DE1) as (gY1 & Eqa1''b1').
  destruct (AnnDefEq_invertb Eqa1''b1') as [AA1'' [b1'' [gb1 [TA1 [TB1 [E1 DE1']]]]]].
  resolve_unique_nosubst.

  assert (AnnPropWff G0 (Eq b0'' b1'' A')). econstructor. eauto. eauto. autorewcs. congruence.

  assert (TEMP : exists g, AnnDefEq G0 D g a0' b0''). eapply (An_Trans' DE0 DE0').
  destruct TEMP as [gY2 Eqa0'b0''].

  assert (TEMP : exists g, AnnDefEq G0 D g a1'' b1''). eapply (An_Trans' Eqa1''b1' DE1').
  destruct TEMP as [gY3 Eqa1''b1''].

  eexists. exists (Eq a0' a1'' A'). exists (Eq b0'' b1'' A').
  split.
  simpl. autorewcs. f_equal; auto.
  split. simpl. autorewcs. f_equal; try congruence.
  simpl. autorewcs. f_equal; auto.
  econstructor; eauto.
- clear d. clear p0. clear p.
  destruct (H G0 H2 H3) as (g & A' & B' & S & EA & EB & ES & DE & TA & TB). clear H.
  destruct (H0 G0 H2 H3) as (phi0 & Ep0 & WF0). clear H0.
  destruct (H1 G0 H2 H3) as (phi1 & Ep1 & WF1). clear H1.
  destruct phi0 as [A1a A2a A''].
  destruct phi1 as [A1b A2b B''].
  simpl in Ep0. inversion Ep0. clear Ep0.
  simpl in Ep1. inversion Ep1. clear Ep1.
  inversion WF0. subst.
  inversion WF1. subst.
  move: (AnnTyping_regularity H8) => R1.
  move: (AnnTyping_regularity H9) => R2.
  move: (AnnTyping_regularity H11) => R3.
  move: (AnnTyping_regularity H12) => R4.

  destruct (AnnDefEq_invert_a_Star DE TA ES) as
      (A''' & B''' & g2 & EA2 & EB2 & DE2 & TAS & TBS).

  simpl in *.
  destruct (erasure_cvt H12) with (B:= A'')   as (A2a' & E2a & T2a); eauto 1.
  (* p1 is (Eq A1a a2a' A''). Want other side to also have type A'' *)
  assert (TMP: exists g, AnnDefEq G0 D g A''' A'').
  { eexists.
    eapply An_EraseEq; eauto 1. congruence. eapply An_Refl; eauto 2. }
  destruct TMP as (ga & EAAA).

  (* convert type of A1b from B'' to A'' *)
  assert (TMP : exists g, AnnDefEq G0 D g B'' A'').
  { eexists. eapply An_Trans2 with (a1 := B''').
    eapply An_EraseEq; eauto 1. congruence. eapply An_Refl; eauto 2.
    eapply An_Trans2 with (a1 := A''').
    eapply An_Sym2; eauto 1.
    eapply An_EraseEq; eauto 1. congruence. eapply An_Refl; eauto 2. }
  destruct TMP as (gb & EBA).

  (* convert type of A2b from B to A'' *)
  assert (TMP : exists g, AnnDefEq G0 D g B A'').
  { eexists. eapply An_Trans2 with (a1 := B''); eauto 1.
    eapply An_EraseEq; eauto 1. eapply An_Refl; eauto 2. }
  destruct TMP as (gc & EBBA).

  eexists. exists (Eq A1a A2a A''). exists (Eq A1b A2b B'').
  repeat split; auto.
  simpl; auto.
  f_equal. congruence. congruence.
  eapply An_IsoConv.
  eapply An_Sym2. eauto 1.
  eapply An_Wff; eauto 1.
  eapply An_Wff; eauto 1.
  congruence.
  congruence.
- (* CPiFst *)
  clear d.
  destruct (H G0 H0 H1) as [g [a0 [b0 [A0' [E1 [E2 [E3 [DE [Ty UT]]]]]]]]]. clear H.
  subst.
  destruct (AnnDefEq_regularity DE) as [A0 [B0 [g0 [TA0 [TB0 DE0]]]]].
  destruct (erase_cpi E1 TA0) as [phi1' [B1' [E [Ephi [EB T1]]]]].
  destruct (erase_cpi E2 TB0) as [phi2' [B2' [E' [Ephi' [EB' T2]]]]].
  resolve_unique_nosubst.
  resolve_unique_nosubst.
  destruct (An_Refl_Star D E T1 Ty E3).
  assert (TB1 : AnnTyping G0 (a_Conv b0 (g_Sym g0)) A0').
  { eapply An_Conv. eauto. eapply An_Sym.
    eapply AnnTyping_regularity. eauto.
    eapply AnnTyping_regularity. eauto.
    eapply An_Refl. eapply An_Star.
    eauto.
    eauto.
    eapply AnnTyping_regularity. eauto.
  }
  assert (E4 : erase (a_Conv b0 (g_Sym g0)) = erase (a_CPi phi2' B2')).
  { simpl. autorewcs. rewrite E'. auto. }
  destruct (An_Refl_Star D E4 T2 TB1 E3).
  assert (exists g, AnnDefEq G0 D g (a_CPi phi1' B1') (a_CPi phi2' B2')).
  { eapply erasure_AnnDefEq with (A'' := a0) (B'' := b0); auto.
    eauto. eauto. eauto.  }
  destruct H2.
  destruct phi1. destruct phi2.
  eexists.
  exists phi1', phi2'.
  destruct phi1'. destruct phi2'. simpl in *.
  repeat split. congruence. congruence.
  eapply An_CPiFst. eapply H2.
- (* assn *)
  rewrite <- H0 in b0.

  destruct (binds_map_3 _ _ _ _ b0) as [s [E2 E3]].
  destruct s; try (simpl in E2; inversion E2).
  destruct phi. simpl in E2. inversion E2.
  subst. clear E2.
  move: (binds_to_AnnPropWff _ _ _ _ H1 E3) => K.
  inversion K. subst.
  move: (AnnTyping_regularity H6) => TA1.
  move: (AnnTyping_regularity H7) => TB0.

  assert (exists g, AnnDefEq G0 (dom G0) g B A0). {
    eexists. eapply An_EraseEq; eauto 1.
    eapply An_Refl; eauto 2.
  }
  destruct H0 as [g' DE].
  assert (AnnTyping G0 (a_Conv b1 g') A0).  eapply An_Conv; eauto 1.
  eexists. exists a0, (a_Conv b1 g'), A0. repeat split.
  eapply An_Trans2 with (a1 := b1); eauto 1.
  eapply An_Assn; eauto.
  eapply An_EraseEq; eauto.
  eauto.
  eauto.
- (* refl *)
  destruct (H G0 H0 H1) as [a0' [A0 [E1 [E2 Ty ]]]]. clear H.
  eexists. exists a0', a0', A0. repeat split; auto. eapply An_Refl. eauto.
- (* sym *)
  destruct (H G0 H0 H1) as [g [a0 [b0 [A0 [E1 [E2 [E3 [DE [Ty TU]]]]]]]]]. clear H.
  destruct (AnnDefEq_invertb DE) as [A0' [b0' [g' [T1 [T2 [T3 T4]]]]]].
  resolve_unique_nosubst.
  assert (exists g, AnnDefEq G0 D g b0' a0).  {
    destruct (An_Sym' DE).
    destruct (An_Sym' T4).
    eapply (An_Trans' H2 H).
  }
  destruct H.
  eexists. exists b0'. exists a0. exists A0. repeat split; auto. congruence. eassumption.
- (* Trans *)
  destruct (H G0 H1 H2) as (g0 & a' & a1' & A0 & E1 & E2 & E3 & DE & Ty & TyU). clear H.
  destruct (H0 G0 H1 H2) as (g1 & a1'' & b' & A1 & E4 & E5 & E6 & DE1 & Ty1 & TyU1). clear H0.
  destruct (AnnDefEq_invertb DE) as (A' & a1''' & g2 & T1 & T2 & E7 & DE2).
  destruct (AnnDefEq_invertb DE1) as (B' & b'' & g3 & T3 & T4 & E8 & DE3).
  subst.
  destruct (An_Trans' DE DE2).
  destruct (An_Trans' DE1 DE3).
  resolve_unique_nosubst.
  resolve_unique_nosubst.
  assert (exists g, AnnDefEq G0 D g a1''' a1'').
  {
    eexists.
    eapply An_EraseEq. eauto. eauto. autorewcs. congruence.
    eapply An_EraseEq. eapply AnnTyping_regularity. eauto.
     eapply AnnTyping_regularity. eauto. eauto.
     eauto.
  }
  destruct H1.
  destruct (An_Trans' H H1).
  destruct (An_Trans' H3 H0).
  destruct (AnnDefEq_invertb H4) as (? & b''' & ? & T3' & T4' & E8' & DE3').
  resolve_unique_nosubst.
  eexists. exists a'. exists b'''. exists A0. repeat split; auto. congruence.
  eapply An_Trans2 with (a1 := b''); eauto 1.
- (* step case *)
  destruct (H G0 H1 H2) as [a1' [A1 [E1 [E2 Ty]]]]. clear H.
  destruct (H0 G0 H1 H2) as [a2' [A2 [E1' [E2' Ty']]]]. clear H0.
  subst.
  assert (exists g, AnnDefEq G0 D g A2 A1).
  { eexists. eapply An_EraseEq.  eapply AnnTyping_regularity. eauto.
    eapply AnnTyping_regularity. eauto. eauto 1.
    eapply An_Refl. eauto 2. }
  destruct H.
  assert (AnnTyping G0 (a_Conv a2' x) A1).
  { eapply An_Conv; eauto 1.
    eapply AnnDefEq_weaken_available; eauto 1.
    eapply AnnTyping_regularity. eauto. }
  eexists. exists a1', (a_Conv a2' x), A1.
  repeat split; eauto 1.
  eapply An_Beta; eauto 1.
- (* pi-cong *)
  clear d. clear d0.
  clear H1. rename H2 into H1. rename H3 into H2. rename H4 into H3. rename H5 into H4.
  destruct (H G0 H3 H4) as (g1 & A1' & A2' & S & EA1 & EA2 & EA3 & DE & T & U). clear H.
  clear H1. clear H2.
  destruct (AnnDefEq_invert_a_Star DE T EA3) as (A1'' & A2'' & g5 & EA5 & EA4 & DE4 & TA1' & TA2').
  assert (erase A1'' = A1). congruence.
  assert (erase A2'' = A2). congruence.

  clear dependent A1'. clear dependent A2'. clear dependent S.

  pick fresh x1.
  assert (FrL : x1 `notin` L). auto.
  assert (CTX1 : AnnCtx ([(x1, Tm A1'')] ++ G0)). eauto with ctx_wff.

  destruct (H0 x1 FrL ([(x1,Tm A1'')] ++ G0)) as (g2 & B1' & B2' & S & EB1 & EB2 & ES & DEB & DT & _); auto.
  { simpl. autorewcs. congruence. } clear H0.

  destruct (AnnDefEq_invert_a_Star DEB DT ES)  as (B1'' & B2'' & g6 & EB3 & EB4 & DE5 & TB1' & TB2'); auto.
  assert (erase B1'' = open_tm_wrt_tm B1 (a_Var_f x1)). congruence.
  assert (erase B2'' = open_tm_wrt_tm B2 (a_Var_f x1)). congruence.
  clear dependent B1'. clear dependent B2'. clear dependent S.

  pick fresh x2.
  remember (close_tm_wrt_tm x1 B2'') as CB2.
  remember (open_tm_wrt_tm CB2 (a_Conv (a_Var_f x2) (g_Sym g5))) as B3.


  assert (CTX2 : AnnCtx ([(x2, Tm A2'')] ++ G0)). eauto with ctx_wff.
  assert (CTX3 : AnnCtx ([(x2, Tm A2'')] ++ [(x1, Tm A1'')] ++ G0)).
  {  eapply An_ConsTm; eauto with ctx_wff.
     eapply (AnnTyping_weakening _ [(x1, Tm A1'')] nil); simpl; eauto with ctx_wff. }


  assert (AnnTyping G0 (a_Pi rho A1'' (close_tm_wrt_tm x1 B1'')) a_Star).
  { eapply An_Pi_exists with (x := x1).
    autorewrite with lngen. clear dependent x2. auto.
    autorewrite with lngen. auto.
    auto. }

  assert (AnnTyping G0 (a_Pi rho A2'' (close_tm_wrt_tm x2 B3)) a_Star).
  { eapply An_Pi_exists with (x := x2).
       autorewrite with lngen. auto.
       rewrite HeqB3. rewrite HeqCB2.
       autorewrite with lngen.
       rewrite -tm_subst_tm_tm_spec.
       replace a_Star with (tm_subst_tm_tm (a_Conv (a_Var_f x2) (g_Sym g5)) x1 a_Star); [|simpl; auto].
       eapply AnnTyping_tm_subst; eauto.
       eapply AnnTyping_weakening with (F := ([(x1, Tm A1'')])); eauto.
       eapply An_ConsTm; eauto.
       eapply AnnTyping_weakening with (F := nil); eauto.
       eapply An_Conv; eauto.
       eapply AnnDefEq_weakening with (F := nil)(G0 := G0).
       eapply (fourth ann_weaken_available_mutual) with (D := dom G0).
       eapply AnnDefEq_weaken_available.
       eauto.
       simpl. clear Fr. clear Fr0. fsetdec.
       eauto. simpl_env. auto.
       eapply AnnTyping_weakening with (F := nil); eauto.
       eauto. }

  exists (g_PiCong rho g5 (close_co_wrt_tm x1 g6)),
  (a_Pi rho A1'' (close_tm_wrt_tm x1 B1'')),
  (a_Pi rho A2'' (close_tm_wrt_tm x2 B3)),
  a_Star.

  repeat split; auto.
  + simpl. rewrite <- close_tm_erase_tm; auto. rewrite H0.
    simpl. rewrite close_tm_wrt_tm_open_tm_wrt_tm; auto. rewrite -H. auto.
  + simpl. f_equal. auto. rewrite <- close_tm_erase_tm; auto. rewrite HeqB3.
    rewrite HeqCB2.
    rewrite <- open_tm_erase_tm.
    rewrite <- close_tm_erase_tm.
    rewrite H2. simpl.
    rewrite close_tm_wrt_tm_open_tm_wrt_tm; auto.
    rewrite close_tm_wrt_tm_open_tm_wrt_tm; auto.
    autorewrite with lngen.
    apply notin_remove_2.
    pose KK := fv_tm_tm_tm_open_tm_wrt_tm_upper B2 (a_Var_f x1). clearbody KK.
    unfold AtomSetImpl.Subset in KK. unfold not.
    intros NN. apply KK in NN.
    apply notin_union in NN. inversion NN. clear KK.
    simpl. auto. auto.
  + eapply An_PiCong_exists with (x1 := x1) (x2 := x2) (B2 := CB2); auto.
    ++ rewrite HeqCB2. autorewrite with lngen. auto.
    ++ rewrite HeqB3. rewrite HeqCB2. autorewrite with lngen.
      apply notin_union; auto.
    ++ rewrite HeqCB2. autorewrite with lngen. auto.
    ++ autorewrite with lngen. auto.
    ++ rewrite HeqCB2. autorewrite with lngen.
       move: (AnnDefEq_context_fv DE5) => /= ?.
       clear Fr Fr0.
       apply An_Pi_exists with (x:=x1).
       +++ apply notin_union. inversion CTX1. auto.
           autorewrite with lngen. fsetdec.
       +++ autorewrite with lngen. auto.
       +++ auto.
- (* abs-cong *)
  clear d. rename H1 into H3. rename H2 into H4.
  destruct (H0 G0 H3 H4) as (A1' & S1 & EA1 & ES & AT). clear H0.
  subst.
  destruct (erasure_a_Star AT ES) as (A1 & EA5 & AT1).
  (*
  destruct (AnnDefEq_invert_a_Star DE AT ES) as (A1 & A2 & gg & EA5 & EA6 & H & AT1 & AT2).
  rewrite -EA5.
  rewrite -EA6.
  rewrite -EA5 in H0.
  clear dependent A1'. clear dependent A2'. clear dependent S.
  *)
  pick fresh x1.
  assert (FrL : x1 `notin` L). auto.
  destruct (H x1 FrL ([(x1,Tm A1)] ++ G0)) as (g2 & b1' & b2' & B' & EB1 & EB2 & S & DEB & TB & TB2); auto. simpl. autorewcs. congruence.

  pick fresh x2.
  remember (close_tm_wrt_tm x1 b2') as b2''.
  remember (g_Refl A1) as gg.
  assert (AnnDefEq G0 D gg A1 A1). { rewrite Heqgg. eauto 3. }
  remember (open_tm_wrt_tm b2'' (a_Conv (a_Var_f x2) (g_Sym gg))) as b3.
  remember (open_tm_wrt_tm (close_tm_wrt_tm x1 B')
                           (a_Conv (a_Var_f x2) (g_Sym gg))) as B3.

  assert (AnnTyping G0 (a_Abs rho A1 (close_tm_wrt_tm x1 b1'))
                    (a_Pi rho A1 (close_tm_wrt_tm x1 B'))).
  { eapply An_Abs_exists with (x := x1).
    + autorewrite with lngen. clear dependent x2. auto.
    + auto.
    + autorewrite with lngen. auto.
    + autorewrite with lngen. autorewcs. rewrite EB1. auto.
  }

  assert (CTX2 : AnnCtx ([(x2, Tm A1)] ++ G0)). eauto with ctx_wff.
  assert (CTX3 : AnnCtx ([(x2, Tm A1)] ++ [(x1, Tm A1)] ++ G0)).
  {  eapply An_ConsTm; eauto.
     eapply (AnnTyping_weakening _ [(x1, Tm A1)] nil); simpl; eauto with ctx_wff.
  }

  assert (AnnTyping G0 (a_Abs rho A1 (close_tm_wrt_tm x2 b3))
                    (a_Pi rho A1 (close_tm_wrt_tm x2 B3))).
  { eapply An_Abs_exists with (x := x2).
    + autorewrite with lngen. auto.
    + auto.
    + rewrite Heqb3. rewrite HeqB3. rewrite Heqb2''. autorewrite with lngen.
      rewrite (tm_subst_tm_tm_intro x1).
      rewrite -(tm_subst_tm_tm_spec B').
      eapply AnnTyping_tm_subst; eauto 1.
      autorewrite with lngen.
      eapply AnnTyping_weakening; eauto 1.
      eapply An_ConsTm; eauto 1.
      eapply AnnTyping_weakening with (F:=nil); eauto 1.
      simpl. eauto.
      eapply An_Conv. eapply An_Var; eauto.
      eapply An_Sym2.
      eapply AnnDefEq_weakening with (F:=nil); eauto 1.
      simpl.
      eapply (fourth ann_weaken_available_mutual) with (D:= dom G0).
      eapply AnnDefEq_weaken_available. eauto.
      clear Fr Fr0. fsetdec.
      eapply AnnTyping_weakening with (F:=nil); eauto 1.
      autorewrite with lngen. eauto.
    + rewrite Heqb3.  rewrite Heqb2''. autorewrite with lngen.
      rewrite (tm_subst_tm_tm_intro x1); auto.
      autorewrite with lngen.
      autorewcs. rewrite -subst_tm_erase_tm; auto. simpl.
      autorewcs. rewrite EB2.
      rewrite -(tm_subst_tm_tm_intro x1); auto.
      autorewrite with lngen. auto.
  }
  assert (TMP: exists g, AnnDefEq G0 D g (a_Pi rho A1 (close_tm_wrt_tm x1 B'))
                        (a_Pi rho A1 (close_tm_wrt_tm x2 B3))).
  { eexists. eapply An_PiCong_exists with (x1:=x1) (x2:=x2)
                                                   (B2 := close_tm_wrt_tm x1 B')
    (g1:= gg) (g2 := (close_co_wrt_tm x1 (g_Refl B'))).
    + simpl. autorewrite with lngen. clear Fr0. auto.
    + autorewrite with lngen.
      apply notin_union. auto.
      rewrite Heqgg. auto.
    + auto.
    + autorewrite with lngen.
      eapply An_Refl.
      eapply AnnTyping_regularity. eauto 1.
    + autorewrite with lngen. auto.
    + eapply AnnTyping_regularity. eauto 1.
    + eapply AnnTyping_regularity. eauto 1.
    + autorewrite with lngen.
      move: (AnnTyping_context_fv TB) => /= ?.
      clear Fr Fr0.
      apply An_Pi_exists with (x := x1).
      apply notin_union. inversion CTX3. inversion H7. auto.
      autorewrite with lngen. fsetdec.
      autorewrite with lngen.
      eapply AnnTyping_regularity. eauto.
      inversion CTX2. auto.
  }
  destruct TMP as [gpi Epipi].
  assert (AnnTyping G0 (a_Conv (a_Abs rho A1 (close_tm_wrt_tm x2 b3)) (g_Sym gpi))
                    (a_Pi rho A1 (close_tm_wrt_tm x1 B'))).
  { eapply An_Conv. eauto 1. eapply An_Sym2.
    eapply AnnDefEq_weaken_available; eauto 1.
    eapply AnnTyping_regularity. eauto 1. }
 eexists. exists
  (a_Abs rho A1 (close_tm_wrt_tm x1 b1')),
  (a_Conv (a_Abs rho A1 (close_tm_wrt_tm x2 b3)) (g_Sym gpi)),
  (a_Pi rho A1 (close_tm_wrt_tm x1 B')).
  repeat split; eauto 1.
  { simpl. f_equal. rewrite <- close_tm_erase_tm; auto. rewrite EB1.
    simpl. rewrite close_tm_wrt_tm_open_tm_wrt_tm; auto. }
  { simpl. f_equal. auto. rewrite <- close_tm_erase_tm; auto.
           rewrite Heqb3. rewrite Heqb2''.
           rewrite <- open_tm_erase_tm.
           rewrite <- close_tm_erase_tm.
           rewrite EB2. simpl.
           rewrite close_tm_wrt_tm_open_tm_wrt_tm; auto.
           rewrite close_tm_wrt_tm_open_tm_wrt_tm; auto.
           autorewrite with lngen.
           apply notin_remove_2.
           pose KK := fv_tm_tm_tm_open_tm_wrt_tm_upper b2 (a_Var_f x1). clearbody KK.
           unfold AtomSetImpl.Subset in KK. unfold not.
           intros NN. apply KK in NN.
           apply notin_union in NN. inversion NN. clear KK.
           simpl. auto. auto.
  }
  { simpl. f_equal. autorewcs. congruence.
    autorewcs. rewrite -close_tm_erase_tm; auto. rewrite S.
    simpl. rewrite close_tm_wrt_tm_open_tm_wrt_tm; auto. }
  { eapply An_Trans2 with (a1 := (a_Abs rho A1 (close_tm_wrt_tm x2 b3))).
    { eapply An_AbsCong_exists with (x1:=x1)(x2:=x2)(b2 := b2'')
          (g1 := gg) (g2 := (close_co_wrt_tm x1 g2))
          (B := a_Pi rho A1 (close_tm_wrt_tm x1 B')).
    + rewrite Heqb2''. autorewrite with lngen. auto.
    + rewrite Heqb3. rewrite Heqb2''. autorewrite with lngen.
      apply notin_union; auto. rewrite Heqgg. auto.
    + auto.
    + rewrite Heqb2''.
      autorewrite with lngen. auto.
    + autorewrite with lngen. auto.
    + auto.
    + auto.
    + autorewrite with lngen. autorewcs. rewrite EB1. auto.
    + rewrite Heqb3. rewrite Heqb2''.
      autorewrite with lngen.
      rewrite (tm_subst_tm_tm_intro x1); auto.
      autorewrite with lngen.
      autorewcs. rewrite -subst_tm_erase_tm; auto. simpl.
      autorewcs. rewrite EB2.
      rewrite -(tm_subst_tm_tm_intro x1); auto.
      autorewrite with lngen. auto.
    + rewrite Heqb2''. autorewrite with lngen.
      clear Fr Fr0.
      move: (AnnTyping_context_fv TB2) => /= ?.
      inversion CTX3. inversion H8. subst.
      eapply An_Abs_exists with (x:= x1).
      autorewrite with lngen.
      fsetdec.
      auto.
      autorewrite with lngen.
      auto.
      autorewrite with lngen.
      { apply An_Abs_inversion in H2.
        destruct H2 as [BB [h0 [h1 h2]]].
        move: (h2 x1 ltac:(auto)) => [h3 _].
        rewrite <- open_tm_erase_tm in h3.
        rewrite <- close_tm_erase_tm in h3.
        rewrite <- open_tm_erase_tm in h3.
        rewrite <- close_tm_erase_tm in h3.
        simpl in h3.
        replace (a_Var_f x2) with (erase_tm (a_Var_f x2)) in h3.
        replace (a_Var_f x1) with (erase_tm (a_Var_f x1)) in h3.
        autorewcshyp h3.
        rewrite close_tm_erase_tm in h3.
        rewrite open_tm_erase_tm in h3.
        replace (a_Var_f x2) with (erase_tm (a_Var_f x2)) in h3.
        rewrite close_tm_erase_tm in h3.
        rewrite open_tm_erase_tm in h3.
        simpl in h3.
        rewrite close_tm_wrt_tm_open_tm_wrt_tm in h3.
        rewrite open_tm_wrt_tm_close_tm_wrt_tm in h3.
        auto.
        autorewrite with lngen.
        move: (AnnTyping_context_fv TB2) => [h5 _].
        simpl in h5. rewrite h5.
        simpl in H10.
        fsetdec.
        auto.
        auto.
        auto.
      }
    }
    eapply An_EraseEq; eauto 1.
    eapply An_Sym. eauto 1.
    eapply AnnTyping_regularity. eauto 1.
    eapply AnnTyping_regularity. eauto 1.
    eapply An_Refl; eauto 2.
    eapply AnnDefEq_weaken_available; eauto 1.
  }
  Unshelve.
  eauto.
  eauto.
- (* appcong *)
  destruct (H G0 H1 H2) as [g1 [a1' [b1' [AB1 [EA1 [EA2 [ET1 [DE1 [TAB1 _]]]]]]]]]. clear H.
  destruct (H0 G0 H1 H2) as [g2 [a2' [b2' [A1 [EA3 [EA4 [ET2 [DE2 [TA1 _]]]]]]]]]. clear H0.
  move: (AnnTyping_regularity TAB1) => TPi.
  destruct (erase_pi ET1 TPi) as (A' & B' & E1 & E2 & E3 & TP).
  inversion  TP. subst.

  destruct (AnnDefEq_regularity DE2) as (A2' & B2' & g3 & ? & Tb2' & DEa2b1).
  resolve_unique_nosubst.

  destruct (erasure_cvt TAB1 E1) as (a1'' & E5 & Ta1''); eauto.
  assert (exists g, AnnDefEq G0 D g a1'' a1').
  { eexists. eapply An_EraseEq. eauto.  eauto. autorewcs. congruence.
    eapply An_EraseEq. eapply AnnTyping_regularity. eauto.
    eapply AnnTyping_regularity. eauto. eauto.
    eapply An_Refl. eauto. }
  destruct H as [g4 DEa1''a1'].
  move: (An_Trans2 DEa1''a1' DE1) => DE4.

  destruct (erasure_cvt TA1) with (B := A') as (a2'' & E4 & Ta2''); eauto.
  assert (exists g, AnnDefEq G0 D g a2'' a2').
  { eexists. eapply An_EraseEq. eauto.  eauto. autorewcs. congruence.
    eapply An_EraseEq. eapply AnnTyping_regularity. eauto.
    eapply AnnTyping_regularity. eauto. eauto.
    eapply An_Refl. eauto. }
  destruct H as [g5 DEa2''a2'].
  move: (An_Trans2 DEa2''a2' DE2) => DE3.

  destruct (AnnDefEq_invertb DE4) as (AB1' & b1'' & g6 & TA1' & TB1' & EB & DE5).
  resolve_unique_nosubst.

  destruct (AnnDefEq_invertb DE3) as (A1'' & b2'' & g7 & TA1'' & TB2'' & EB1 & DE6).
  resolve_unique_nosubst.

  assert (TT : AnnTyping G0 (a_App a1'' Rel a2'') (open_tm_wrt_tm B' a2'')).
  { eapply An_App. eauto. eauto. }

  assert (AnnTyping G0 (a_App b1'' Rel b2'') (open_tm_wrt_tm B' b2'')).
  { eapply An_App. eauto. eauto. }

  assert (exists g, AnnDefEq G0 D g a2'' b2'').
  { eexists. eapply An_Trans2. eauto. eauto. }
  destruct H0 as [g8 Eab].

  assert (exists g, AnnDefEq G0 D g (open_tm_wrt_tm B' a2'') (open_tm_wrt_tm B' b2'')).
  { eexists. eapply An_PiSnd; eauto 1.
    eapply An_Refl. eapply AnnTyping_regularity. eauto 1. }
  destruct H0 as [g9 HBB].

  assert (AnnTyping G0 (a_Conv (a_App b1'' Rel b2'') (g_Sym g9)) (open_tm_wrt_tm B' a2'')).
  { eapply An_Conv; eauto 1. eapply An_Sym2.
    eapply AnnDefEq_weaken_available; eauto 1.
    eapply AnnTyping_regularity. eauto. }

  eexists.
  exists (a_App a1'' Rel a2'').
  exists (a_Conv (a_App b1'' Rel b2'') (g_Sym g9)).
  exists (open_tm_wrt_tm B' a2'').
  repeat split.
  simpl. autorewcs. congruence.
  simpl. autorewcs. congruence.
  rewrite -open_tm_erase_tm.
  f_equal. auto.
  { eapply An_Trans2 with (a1 := (a_App b1'' Rel b2'')).
    eapply An_AppCong; eauto 1.
    eapply An_Trans2 with (a1 := b1'); eauto 2.
    eapply AnnDefEq_weaken_available; eauto 1.
    eapply An_EraseEq; eauto 2.
    eapply An_Sym.
    eapply AnnTyping_regularity. eauto.
    eapply AnnTyping_regularity. eauto.
    eapply An_Refl. eauto 2.
    eapply AnnDefEq_weaken_available; eauto 1.
    }
  eauto.
  eauto.
- (* iappcong *)
  destruct (H G0 H1 H2) as [g1 [a1' [b1' [AB1 [EA1 [EA2 [ET1 [DE1 [TAB1 _]]]]]]]]]. clear H.
  destruct (H0 G0 H1 H2) as (a2' & A1 & EA3 & ET2 & TA1). clear H0.
  move: (AnnTyping_regularity TAB1) => TPi.
  destruct (erase_pi ET1 TPi) as (A' & B' & E1 & E2 & E3 & TP).
  inversion  TP. subst.

  destruct (erasure_cvt TAB1 E1) as (a1'' & E5 & Ta1''); eauto.
  assert (exists g, AnnDefEq G0 D g a1'' a1').
  { eexists. eapply An_EraseEq. eauto.  eauto. autorewcs. congruence.
    eapply An_EraseEq. eapply AnnTyping_regularity. eauto.
    eapply AnnTyping_regularity. eauto. eauto.
    eapply An_Refl. eauto. }
  destruct H as [g4 DEa1''a1'].
  move: (An_Trans2 DEa1''a1' DE1) => DE4.

  destruct (erasure_cvt TA1) with (B := A') as (a2'' & E4 & Ta2''); eauto.
  assert (exists g, AnnDefEq G0 D g a2'' a2').
  { eexists. eapply An_EraseEq. eauto.  eauto. autorewcs. congruence.
    eapply An_EraseEq. eapply AnnTyping_regularity. eauto.
    eapply AnnTyping_regularity. eauto. eauto.
    eapply An_Refl. eauto. }
  destruct H as [g5 DEa2''a2'].

  destruct (AnnDefEq_invertb DE4) as (AB1' & b1'' & g6 & TA1' & TB1' & EB & DE5).
  resolve_unique_nosubst.

  assert (TT : AnnTyping G0 (a_App a1'' Irrel a2'') (open_tm_wrt_tm B' a2'')).
  { eapply An_App. eauto. eauto. }

  assert (AnnTyping G0 (a_App b1'' Irrel a2'') (open_tm_wrt_tm B' a2'')).
  { eapply An_App. eauto. eauto. }

  eexists.
  exists (a_App a1'' Irrel a2'').
  exists (a_App b1'' Irrel a2'').
  exists (open_tm_wrt_tm B' a2'').
  repeat split.
  simpl. autorewcs. congruence.
  simpl. autorewcs. congruence.
  rewrite -open_tm_erase_tm.
  f_equal. auto.
  { eapply An_Trans2 with (a1 := (a_App b1'' Irrel a2'')).
    eapply An_AppCong; eauto 1.
    eapply An_Trans2 with (a1 := b1'); eauto 2.
    eapply An_Refl; eauto 2.
    eapply An_Refl; eauto 2.
    eapply AnnTyping_regularity. eauto 2.
    eapply An_Refl; eauto 2.
    }
  eauto.
  eauto.
- destruct (H G0 H0 H1) as [g [AB1 [AB2 [S1 [E1 [E2 [E3 [DE [T1 _]]]]]]]]].
  clear H.
  destruct (AnnDefEq_regularity DE) as [S2 [S2' [g1 [T2 [T3 DE2]]]]].
  resolve_unique_nosubst.
  destruct (erase_pi E1 T1) as [A1' [B1' [F1 [F2 [F3 AT]]]]].
  destruct (erase_pi E2 T3) as [A2' [B2' [F1' [F2' [F3' AT']]]]].
  subst.
  destruct (erasure_AnnDefEq DE T1 E3 F1 F1' AT AT')
    as (g2 & DE3).
  inversion AT. inversion AT'. subst.
  eexists. exists A1', A2', a_Star.
  repeat split. eauto. eauto. auto.
- (* PiSnd *)
  clear d. clear d0.
  destruct (H G0 H1 H2) as [g [AB1 [AB2 [S1 [E1 [E2 [E3 [DE1 [AT1 _]]]]]]]]]. clear H.
  destruct (H0 G0 H1 H2) as [g1 [a1' [a2' [S2 [E1' [E2' [E3' [DE2 [AT2 _]]]]]]]]]. clear H0.
  destruct (AnnDefEq_regularity DE1) as [SS1 [SS2 [g4 [T3 [T4 DE3]]]]].
  destruct (erase_pi E1 T3) as [A14 [A24 [F1 [F2 [F3 AT]]]]].
  destruct (erase_pi E2 T4) as [A15 [A25 [F1' [F2' [F3' AT']]]]].
  inversion AT. subst.
  inversion AT'. subst.

  (* Get equality between Pi types *)
  destruct (erasure_AnnDefEq DE1 AT1 E3 F1 F1' AT) as (g6 & DE5). eauto.
  resolve_unique_nosubst.

  (* a1 of domain type A14 *)
  destruct (erasure_cvt AT2 (symmetry F2)) as [a1 [EA1 TA1]]. eauto.
  (* a2 of domain type A15 *)
  destruct (AnnDefEq_invertb DE2) as (S3 & a2'' & g7 & T5 & T6 & ? & DE6).
  resolve_unique_nosubst.
  destruct (erasure_cvt T6 (symmetry F2)) as [a2''' [EA2 TA2]]. eauto.
  assert (AnnDefEq G0 D (g_PiFst g6) A14 A15).
  { eapply An_PiFst. eauto. }
  remember (a_Conv a2''' (g_PiFst g6)) as a2.
  assert (AnnTyping G0 a2 A15).
  { rewrite Heqa2. eapply An_Conv; eauto.
    eapply AnnDefEq_weaken_available. eauto. }
  (* a1 ~ a2 *)
  assert (TEMP : exists g, AnnDefEq G0 D g a1 a1').
  { eexists. eapply An_EraseEq; eauto 1.
    eapply An_EraseEq; eauto 1.
    eapply AnnTyping_regularity; eauto.
    eapply An_Refl. eauto. }
  destruct TEMP as (? & Ha1a1').

  assert (TEMP : exists g, AnnDefEq G0 D g a2'' a2''').
  {  eexists.
    eapply An_EraseEq; eauto 1.
    eapply An_EraseEq; eauto 1.
    eapply AnnTyping_regularity; eauto.
    eapply An_Refl. eauto. }
  destruct TEMP as (? & Ha2''a2''').
  assert (TEMP : exists g, AnnDefEq G0 D g a2''' a2).
  { rewrite Heqa2.
    eexists.
    eapply An_EraseEq. eauto.
    rewrite -Heqa2. eauto.
    eauto.
    eapply AnnDefEq_weaken_available. eauto.
  }
  destruct TEMP as (? & Ha2'''a2).
  move: (An_Trans2 Ha1a1' DE2) => Ha1a2'.
  move: (An_Trans2 Ha1a2' DE6) => Ha1a2''.
  move: (An_Trans2 Ha1a2'' Ha2''a2''') => Ha1a2'''.
  move: (An_Trans2 Ha1a2''' Ha2'''a2) => Ha1a2.
  eexists.
  exists (open_tm_wrt_tm  A24 a1).
  exists (open_tm_wrt_tm  A25 a2).
  exists a_Star.
  repeat split.
  rewrite <- open_tm_erase_tm. congruence.
  rewrite <-  open_tm_erase_tm. rewrite Heqa2. simpl.
  f_equal. autorewcs. congruence.
  eapply An_PiSnd; eauto.
  pick fresh x2 for (L \u fv_tm_tm_tm A24).
  rewrite (tm_subst_tm_tm_intro x2); auto.
  replace a_Star with (tm_subst_tm_tm a1 x2 a_Star).
  eapply AnnTyping_tm_subst.
  eapply H4. auto. auto. simpl. auto.
  pick fresh x2 for (L0 \u fv_tm_tm_tm A25).
  rewrite (tm_subst_tm_tm_intro x2); auto.
  replace a_Star with (tm_subst_tm_tm a2 x2 a_Star).
  eapply AnnTyping_tm_subst.
  eapply H3. auto. auto. simpl. auto.
- (* CPiCong *)
  idtac. rename A into B1. rename B into B2.
  clear H1. rename H2 into H1. rename H3 into H2. rename H4 into H3. rename H5 into H4.
  clear d. clear i.
  destruct (H G0 H3 H4) as (g1 & phi1' & phi2' & EP1 & EP2 & IP). clear H.
  clear H1 H2. rename H3 into H1. rename H4 into H2.
  destruct (AnnIso_regularity IP) as [WFF1 WFF2].
  inversion WFF1. inversion WFF2. subst.

  move: (AnnTyping_regularity H) => ?.
  move: (AnnTyping_regularity H7) => ?.
  move: (AnnTyping_regularity H3) => ?.
  move: (AnnTyping_regularity H8) => ?.

  assert (exists g, AnnDefEq G0 D g A0 B0).
  { eexists. eapply An_EraseEq; eauto 1. eauto. }
  destruct H1 as [g2 EA0B0].
  assert (exists g, AnnDefEq G0 D g A B).
  { eexists. eapply An_EraseEq; eauto 1. eauto. }
  destruct H1 as [g3 EAB].

  pick fresh x1.
  assert (FrL : x1 `notin` L). auto.
  assert (CTX1 : AnnCtx ([(x1, Co (Eq a b A))] ++ G0)). eauto with ctx_wff.

  destruct (H0 x1 FrL ([(x1,Co (Eq a b A))] ++ G0)) as (g4 & B1' & B2' & S & EB1 & EB2 & ES & DEB & DT & _); auto.
  clear H0.

  destruct (AnnDefEq_invert_a_Star DEB DT ES)  as (B1'' & B2'' & g6 & EB3 & EB4 & DE5 & TB1' & TB2'); auto.
  assert (erase B1'' = open_tm_wrt_co B1 (g_Var_f x1)). congruence.
  assert (erase B2'' = open_tm_wrt_co B2 (g_Var_f x1)). congruence.
  clear dependent B1'. clear dependent B2'. clear dependent S.

  pose AVOID := erase B2''.
  pick fresh x2.
  remember (close_tm_wrt_co x1 B2'') as CB2.
  remember (open_tm_wrt_co CB2 (g_Cast (g_Var_f x2) (g_Sym g1))) as B3.


  assert (CTX2 : AnnCtx ([(x2, Co (Eq a0 b0 A0))] ++ G0)). eauto with ctx_wff.
  assert (CTX3 : AnnCtx ([(x2, Co (Eq a0 b0 A0))] ++ [(x1, Co (Eq a b A))] ++ G0)).
  {  eapply An_ConsCo; eauto.
     eapply (AnnPropWff_weakening _ [(x1, Co (Eq a b A))] nil); simpl; eauto. }


  assert (AnnTyping G0 (a_CPi (Eq a b A) (close_tm_wrt_co x1 B1'')) a_Star).
  { eapply An_CPi_exists with (c := x1).
    autorewrite with lngen. clear dependent x2. auto.
    autorewrite with lngen. auto.
    autorewrite with lngen. eauto.
  }

  assert (AnnTyping G0 (a_CPi (Eq a0 b0 A0) (close_tm_wrt_co x2 B3)) a_Star).
  { eapply An_CPi_exists with (c := x2).
    autorewrite with lngen. auto.
    eauto.
    rewrite HeqB3. rewrite HeqCB2.
    autorewrite with lngen.
    rewrite -co_subst_co_tm_spec.
    replace a_Star with (co_subst_co_tm (g_Cast (g_Var_f x2) (g_Sym g1)) x1 a_Star); [|simpl; auto].
    eapply AnnTyping_co_subst with (D := dom ([(x2, Co (Eq a0 b0 A0))] ++ G0)); eauto.
    eapply AnnTyping_weakening with (F := ([(x1, Co (Eq a b A))])); eauto 1.
    eapply An_ConsCo; eauto.
    eapply AnnPropWff_weakening with (F := nil); eauto.
    eapply An_Cast; eauto 2.
    eapply An_Assn; eauto.
    simpl. simpl_env.
    eapply AnnIso_weakening with (F := nil)(G0 := G0).
    eapply (third ann_weaken_available_mutual) with (D := dom G0).
    eapply AnnIso_weaken_available.
    eauto.
    simpl. clear Fr Fr0. fsetdec.
    eauto. simpl_env. auto.
 }


  exists (g_CPiCong g1 (close_co_wrt_co x1 g6)),
  (a_CPi (Eq a b A) (close_tm_wrt_co x1 B1'')),
  (a_CPi (Eq a0 b0 A0) (close_tm_wrt_co x2 B3)),
  a_Star.

  repeat split.
  + simpl. rewrite <- close_co_erase_tm; auto. rewrite H0.
    simpl. rewrite close_tm_wrt_co_open_tm_wrt_co; auto.
  + simpl. f_equal. rewrite <- close_co_erase_tm; auto. rewrite HeqB3.
    rewrite HeqCB2.
    rewrite <- (open_co_erase_tm2 _ _ (g_Var_f x2)).
    simpl. rewrite close_tm_wrt_co_open_tm_wrt_co.
    rewrite <- close_co_erase_tm.
    rewrite H1.
    simpl. rewrite close_tm_wrt_co_open_tm_wrt_co.
    auto.
    clear Fr0. auto.
    rewrite <- close_co_erase_tm.
    autorewrite with lngen.
    apply notin_remove_2.
    auto.
  + eapply An_CPiCong_exists with (c1 := x1) (c2 := x2) (B2 := CB2).
    ++ auto.
    ++ rewrite HeqCB2. autorewrite with lngen. auto.
    ++ rewrite HeqB3. rewrite HeqCB2. autorewrite with lngen.
      apply notin_union; auto.
    ++ rewrite HeqCB2. autorewrite with lngen. auto.
    ++ rewrite HeqB3. rewrite HeqCB2. autorewrite with lngen.
       auto.
    ++ auto.
    ++ auto.
    ++ rewrite HeqCB2. autorewrite with lngen.
       clear Fr Fr0.
       move: (AnnDefEq_context_fv DE5) => /= ?.
       inversion CTX1. subst.
       eapply An_CPi_exists with (c:=x1).
       autorewrite with lngen.
       fsetdec.
       auto.
       autorewrite with lngen.
       auto.
  + auto.
  + auto.
- (* CAbsCong *)
  rename a into B1. rename b into B2. rename B into S.
  (*clear H1. rename H2 into H1. rename H3 into H2.*)
  destruct (H0 G0 H1 H2) as (phi1' & EP1 & WFF1). clear H0.
  inversion WFF1. subst.

  move: (AnnTyping_regularity H0) => ?.
  move: (AnnTyping_regularity H3) => ?.

  assert (exists g, AnnDefEq G0 D g A B).
  { eexists. eapply An_EraseEq; eauto 1. eauto. }
  destruct H1 as [g3 EAB].

  pick fresh x1.
  assert (FrL : x1 `notin` L). auto.
  assert (CTX1 : AnnCtx ([(x1, Co (Eq a b A))] ++ G0)). eauto with ctx_wff.

  destruct (H x1 FrL ([(x1,Co (Eq a b A))] ++ G0)) as (g4 & B1' & B2' & C1 & EB1 & EB2 & ES & DEB & DT & DU); auto.
  clear H.

  destruct (AnnDefEq_regularity DEB) as (? & C2 & g &  ? & TB2 & DEC).
  resolve_unique_nosubst.
  resolve_unique_nosubst.


  pose AVOID := erase B2'.
  pick fresh x2.
  remember (close_tm_wrt_co x1 B2') as CB2.
  have refl: exists g, AnnIso G0 D g (Eq a b A) (Eq a b A).
  { eexists. apply An_PropCong. eapply An_Refl. eassumption. eapply An_Refl. eassumption.
    apply WFF1. apply WFF1. }
    destruct refl as [g1 refl].
    remember (open_tm_wrt_co CB2 (g_Cast (g_Var_f x2) (g_Sym g1))) as B3.
    remember (open_tm_wrt_co (close_tm_wrt_co x1 C1)
                           (g_Cast (g_Var_f x2) (g_Sym g1))) as C3.

  assert (CTX2 : AnnCtx ([(x2, Co (Eq a b A))] ++ G0)). eauto 2 with ctx_wff.
  assert (CTX3 : AnnCtx ([(x2, Co (Eq a b A))] ++ [(x1, Co (Eq a b A))] ++ G0)).
  {  eapply An_ConsCo; eauto 1.
     eapply (AnnPropWff_weakening _ [(x1, Co (Eq a b A))] nil); simpl; eauto. }

    assert (AnnTyping G0 (a_CAbs (Eq a b A)
                               (close_tm_wrt_co x1 B1')) (a_CPi (Eq a b A) (close_tm_wrt_co x1 C1))).
  { eapply An_CAbs_exists with (c := x1).
    autorewrite with lngen. clear dependent x2.
    apply notin_union; auto.
    auto.
    autorewrite with lngen. auto.
  }


  assert (AnnTyping G0 (a_CAbs (Eq a b A) (close_tm_wrt_co x2 B3))
                      (a_CPi (Eq a b A) (close_tm_wrt_co x2 C3))).
  { eapply An_CAbs_exists with (c := x2).
    autorewrite with lngen. auto.
    eauto.
    rewrite HeqB3. rewrite HeqCB2. rewrite HeqC3.
    autorewrite with lngen.
    rewrite -co_subst_co_tm_spec.
    rewrite -co_subst_co_tm_spec.
    eapply AnnTyping_co_subst with (D := dom ([(x2, Co (Eq a b A))] ++ G0)); eauto.
    eapply AnnTyping_weakening with (F := ([(x1, Co (Eq a b A))])); eauto 1.
    eapply An_ConsCo; eauto.
    eapply AnnPropWff_weakening with (F := nil); eauto.
    eapply An_Cast; eauto 2.
    eapply An_Assn; eauto.
    simpl; eauto 2.
    simpl_env.
    eapply AnnIso_weakening with (F := nil)(G0 := G0).
    eapply (third ann_weaken_available_mutual) with (D := dom G0).
    eapply AnnIso_weaken_available.
    eauto.
    simpl. clear Fr Fr0. fsetdec.
    eauto. simpl_env. auto.
  }

  assert (exists g, AnnDefEq ([(x1, Co (Eq a b A))] ++ G0) (dom G0) g C1 C1).
  { eexists. eapply An_Refl.
    eapply AnnTyping_regularity. eauto 1. }
  destruct H5 as [ grefl EC1C1].
  assert (exists g, AnnDefEq G0 (dom G0) g
                        (a_CPi (Eq a b A) (close_tm_wrt_co x1 C1))
                        (a_CPi (Eq a b A) (close_tm_wrt_co x2 C3))).
  {
    eexists. eapply An_CPiCong_exists with
             (c1 := x1)
               (c2 := x2)
               (B2 := close_tm_wrt_co x1 C1)
               (g3 := close_co_wrt_co x1 grefl).
    + eapply AnnIso_weaken_available. eauto 1.
    + simpl. autorewrite with lngen. clear Fr0. auto.
    + autorewrite with lngen.
      apply notin_union.
      pose M := AnnIso_context_fv refl.
      clearbody M.
      destruct M as [_ [h4 _]].
      unfold "[<=]" in h4.
      move => h6.
      have h1: x2 `notin` dom G0; auto.
      auto 3.
    + autorewrite with lngen. eauto 1.
    + rewrite HeqC3. autorewrite with lngen. auto.
    + eapply AnnTyping_regularity; eauto 1.
    + eapply AnnTyping_regularity; eauto 1.
    + autorewrite with lngen.
      clear Fr Fr0.
      move: (AnnTyping_context_fv DT) => /= ?.
      inversion CTX3. inversion H8. subst.
      eapply An_CPi_exists with (c:=x1).
      autorewrite with lngen.
      fsetdec.
      auto.
      autorewrite with lngen.
      eapply AnnTyping_regularity. eauto.
  }
  destruct H5 as [g5 Epipi].

  assert (AnnTyping G0
                    (a_Conv (a_CAbs (Eq a b A) (close_tm_wrt_co x2 B3))
                            (g_Sym g5))
                    (a_CPi (Eq a b A) (close_tm_wrt_co x1 C1))).
  { eapply An_Conv; eauto 1.
    eapply An_Sym2; auto.
    eapply AnnTyping_regularity; eauto 1. }

  eexists.
  exists (a_CAbs (Eq a b A) (close_tm_wrt_co x1 B1')),
  (a_Conv (a_CAbs (Eq a b A) (close_tm_wrt_co x2 B3)) (g_Sym g5)),
  (a_CPi (Eq a b A) (close_tm_wrt_co x1 C1)).

  repeat split.
  + simpl. rewrite <- close_co_erase_tm; auto. rewrite EB1.
    simpl. rewrite close_tm_wrt_co_open_tm_wrt_co; auto.
  + simpl. f_equal. rewrite <- close_co_erase_tm; auto. rewrite HeqB3.
    rewrite HeqCB2.
    rewrite <- (open_co_erase_tm2 _ _ (g_Var_f x2)).
    simpl. rewrite close_tm_wrt_co_open_tm_wrt_co.
    rewrite <- close_co_erase_tm.
    rewrite EB2.
    simpl. rewrite close_tm_wrt_co_open_tm_wrt_co.
    auto.
    clear Fr0. auto.
    rewrite <- close_co_erase_tm.
    autorewrite with lngen.
    apply notin_remove_2.
    auto.
  + simpl. f_equal.
    rewrite <- close_co_erase_tm; auto. rewrite ES.
    simpl. rewrite close_tm_wrt_co_open_tm_wrt_co; auto.

  + eapply An_Trans2 with (a1 := (a_CAbs (Eq a b A)(close_tm_wrt_co x2 B3))).
    eapply An_CAbsCong_exists with (c1 := x1) (c2 := x2) (a2 := CB2)
       (g3 := close_co_wrt_co x1 g4)
       (B := a_CPi (Eq a b A) (close_tm_wrt_co x1 C1));
      eauto 1.
    ++ rewrite HeqCB2. autorewrite with lngen. auto.
    ++ autorewrite with lngen.
       apply notin_union.
       pose M := AnnIso_context_fv refl.
       clearbody M.
       destruct M as [_ [h4 _]].
       unfold "[<=]" in h4.
       move => h6.
       have h1: x2 `notin` dom G0; auto.
       rewrite HeqCB2. autorewrite with lngen.
       auto 3.
    ++ rewrite HeqCB2. autorewrite with lngen. auto.
    ++ rewrite HeqB3. rewrite HeqCB2. autorewrite with lngen.
       auto.
    ++ autorewrite with lngen.
       clear Fr Fr0.
       subst CB2.
       inversion CTX3. inversion H9. subst.
       eapply An_CAbs_exists with (c:=x1).
       autorewrite with lngen. fsetdec.
       auto.
       autorewrite with lngen. auto.
    ++ eapply An_EraseEq; eauto 1.
       eapply An_Sym2; eauto 1.
  + eauto 1.
  + eauto 1.
    Unshelve.
    eauto 1.
    eauto 1.
- (* CAppCong *)
  clear d.

  destruct (H G0 H1 H2) as [g1 [a1' [b1' [AB1 [EA1 [EA2 [ET1 [DE1 [TAB1 _]]]]]]]]]. clear H.
  move: (AnnTyping_regularity TAB1) => TPi.
  destruct (erase_cpi ET1 TPi) as (A' & B' & E1 & E2 & E3 & TP).
  inversion  TP.

  destruct A' as [a2'' b2'']. simpl in E2. inversion E2. clear E2.
  inversion H5.

  destruct (H0 G0 H1 H2) as [g2 [a2' [b2' [A1' [EA3 [EA4 [ET2 [DE2 [TA1 _]]]]]]]]]. clear H0.
  subst.

  move: (AnnTyping_regularity H14) => SA1.
  move: (AnnTyping_regularity H15) => ?.
  move: (AnnTyping_regularity TA1) => SA1'.

 (* Make sure func has the cpi-type *)
 destruct (erasure_cvt TAB1 E1) as (a1'' & E5 & Ta1''); eauto.
  assert (exists g, AnnDefEq G0 D g a1'' a1').
  { eexists. eapply An_EraseEq. eauto.  eauto. autorewcs. congruence.
    eapply An_EraseEq. eapply AnnTyping_regularity. eauto.
    eapply AnnTyping_regularity. eauto. eauto.
    eapply An_Refl. eauto. }
  destruct H as [g4 DEa1''a1'].
  move: (An_Trans2 DEa1''a1' DE1) => DE4.

  (* Find the coercion that corresponds to that prop.  *)
  destruct (AnnDefEq_regularity DE2) as (? & B2' & g3 & ? & Tb2' & DEa2b1).
  move: (AnnTyping_regularity Tb2') => ?.
  resolve_unique_nosubst.

  assert (exists g, AnnDefEq G0 (dom G0) g a2'' a2').
  { eexists. eapply An_EraseEq; eauto 1.
    eapply An_EraseEq; eauto 1. eapply An_Refl. eauto. }
  destruct H as [g5 Ea2''a2'].


  assert (exists g, AnnDefEq G0 (dom G0) g A0 B1).
  { eexists. eapply An_EraseEq; eauto 1. eapply An_Refl. eauto. }
  destruct H as [g6 EA1B1].

  assert (exists g, AnnDefEq G0 (dom G0) g A1' A0).
  { eexists. eapply An_EraseEq; eauto 1. eapply An_Refl. eauto. }
  destruct H as [g7 EA1'A1].

  (* Make b'' have the same type as b2' *)

  assert (exists g, AnnDefEq G0 (dom G0) g b2' b2'').
  { eexists. eapply An_EraseEq; eauto 1.
    eapply An_Trans2 with (a1 := A1').
    eapply An_Sym2; eauto 1.
    eapply An_Trans2 with (a1 := A0);
      eauto 1.
      }
  destruct H as [g8 Eb2'b2''].

  rewrite -erase_dom in DE2.
  move: (An_Trans2 Ea2''a2' (An_Trans2 DE2 Eb2'b2'')) => Ea2''b2''.
  remember (g_Trans g5 (g_Trans g2 g8)) as g9.

  (* Find b1' type as a CPi type *)
  destruct (AnnDefEq_invertb DE4) as (? & b1'' & g10 & ? & Tb1'' & E6 & DEBB).
  resolve_unique_nosubst.

  assert (TT : AnnTyping G0 (a_CApp a1'' g9) (open_tm_wrt_co B' g9)).
  { eapply An_CApp. eauto. eauto. }

  assert (AnnTyping G0 (a_CApp b1'' g9) (open_tm_wrt_co B' g9)).
  { eapply An_CApp. eauto. eauto. }

  eexists.
  exists (a_CApp a1'' g9).
  exists (a_CApp b1'' g9).
  exists (open_tm_wrt_co B' g9).
  repeat split.
  simpl. f_equal. eauto 1.
  simpl. f_equal. eauto 2.
  rewrite <- (open_co_erase_tm2 _ _ g_Triv). auto.

  eapply An_CAppCong; eauto 2.
  eapply An_Trans2 with (a1 := b1'); eauto 1.
  eapply An_Refl. eapply AnnTyping_regularity; eauto 1.
  assumption.
  assumption.
- (* CPiSnd *)
  clear d. clear d1. clear d0.
  rename a1' into b1. rename a2' into b2. rename A' into B.
  destruct (H G0 H2 H3) as [g [AB1 [AB2 [S1 [E1 [E2 [E3 [DE1 [T1 _]]]]]]]]]. clear H.
  destruct (H0 G0 H2 H3) as [g1 [a1' [a2' [A' [EA11 [EA21 [E31 [DEA [T1A _]]]]]]]]]. clear H0.
  destruct (H1 G0 H2 H3) as [g1' [b1' [b2' [B' [EA11' [EA21' [E31' [DEA' [T1A' _]]]]]]]]]. clear H1.

  destruct (AnnDefEq_regularity DE1) as [S1' [S2' [g4 [T3 [T4 DE3]]]]].
  destruct (AnnDefEq_regularity DEA) as [S1'' [S2'' [g5 [T3' [T4' DE3']]]]].
  destruct (AnnDefEq_regularity DEA') as [S1''' [S2''' [g5' [T3'' [T4'' DE3'']]]]].
  resolve_unique_nosubst.
  resolve_unique_nosubst.
  resolve_unique_nosubst.

  move: (AnnTyping_regularity T1A) => ?.
  move: (AnnTyping_regularity T1A') => ?.
  move: (AnnTyping_regularity T4) => ?.
  move: (AnnTyping_regularity T4') => ?.

  destruct (erase_cpi E1 T1) as [phi1' [B1' [F1 [F2 [F3 AT]]]]].
  destruct (erase_cpi E2 T4) as [phi2' [B2' [F1' [F2' [F3' AT']]]]].
  destruct phi1' as [a1'' a2'' A'']. simpl in F2. inversion F2. clear F2.
  destruct phi2' as [b1'' b2'' B'']. simpl in F2'. inversion F2'. clear F2'.

  destruct (erasure_AnnDefEq DE1 T1 E3  F1 F1' AT AT') as [g2 DE2].
  inversion AT. inversion AT'.
  inversion H10. inversion H15.
  subst.

  (* Have the equality between the CPi types. Now we need to get the
     coercions to match them.
   *)
  assert (TMP : exists g, AnnDefEq G0 D g a1'' a1').
  { eexists. eapply An_EraseEq; eauto 1.
    eapply An_EraseEq.
    eapply AnnTyping_regularity; eauto 1.
    eapply AnnTyping_regularity; eauto 1.
    eauto 1.
    eapply An_Refl; eauto 2. }
  destruct TMP as [g3 Ea1''a1'].
  assert (TMP : exists g, AnnDefEq G0 (dom G0) g A'' B4).
  { eexists. eapply An_EraseEq.
    eapply AnnTyping_regularity; eauto 1.
    eapply AnnTyping_regularity; eauto 1.
    eauto 1.
    eapply An_Refl; eauto 2. }
  destruct TMP as [g6 EA''B4].
 assert (TMP : exists g, AnnDefEq G0 (dom G0) g A' A'').
  { eexists. eapply An_EraseEq.
    eapply AnnTyping_regularity; eauto 1.
    eapply AnnTyping_regularity; eauto 1.
    eauto 1.
    eapply An_Refl; eauto 2. }
  destruct TMP as [g7 EA'A''].

  move: (An_Trans2 (An_Sym2 DE3') (An_Trans2 EA'A'' EA''B4)) => ?.
  assert (TMP : exists g, AnnDefEq G0 D g a2' a2'').
  { eexists. eapply An_EraseEq; eauto 1. }
  destruct TMP as [g8 Ea2'a2''].

  move: (AnnDefEq_weaken_available Ea1''a1') => y.
  rewrite erase_dom in y.
  move: (AnnDefEq_weaken_available Ea2'a2'') => x.
  rewrite erase_dom in x.
  move: (An_Trans2 y (An_Trans2 DEA x)) => Ea1''a2''.

  assert (TMP : exists g, AnnDefEq G0 D g b1'' b1').
  { eexists. eapply An_EraseEq; eauto 1.
    eapply An_EraseEq.
    eapply AnnTyping_regularity; eauto 1.
    eapply AnnTyping_regularity; eauto 1.
    eauto 1.
    eapply An_Refl; eauto 2. }
  destruct TMP as [g9 Eb1'Eb1''].
  (* WANT S''' B5 *)


  assert (TMP : exists g, AnnDefEq G0 (dom G0) g B'' B5).
  { eexists. eapply An_EraseEq.
    eapply AnnTyping_regularity; eauto 1.
    eapply AnnTyping_regularity; eauto 1.
    eauto 1.
    eapply An_Refl; eauto 2. }
  destruct TMP as [g10 EB''B5].
 assert (TMP : exists g, AnnDefEq G0 (dom G0) g B' B'').
  { eexists. eapply An_EraseEq.
    eapply AnnTyping_regularity; eauto 1.
    eapply AnnTyping_regularity; eauto 1.
    eauto 1.
    eapply An_Refl; eauto 2. }
  destruct TMP as [g11 EB'B''].

  move: (An_Trans2 (An_Sym2 DE3'') (An_Trans2 EB'B'' EB''B5)) => ?.
  assert (TMP : exists g, AnnDefEq G0 D g b2' b2'').
  { eexists. eapply An_EraseEq; eauto 1. }
  destruct TMP as [g12 Eb2'b2''].

  assert (TMP : exists g, AnnDefEq G0 D g b1'' b1').
  { eexists. eapply An_EraseEq; eauto 1.
    eapply An_EraseEq.
    eapply AnnTyping_regularity; eauto 1.
    eapply AnnTyping_regularity; eauto 1.
    eauto 1.
    eapply An_Refl; eauto 2. }
  destruct TMP as [g13 Eb1''b1'].


  move: (AnnDefEq_weaken_available Eb2'b2'') => y1.
  rewrite erase_dom in y1.
  move: (AnnDefEq_weaken_available Eb1''b1') => x1.
  rewrite erase_dom in x1.

  move: (An_Trans2 x1 (An_Trans2 DEA' y1)) => Eb1''b2''.
  clear x1. clear y1.
  eexists.
  exists
    (open_tm_wrt_co B1' (g_Trans g3 (g_Trans g1 g8))),
    (open_tm_wrt_co B2' (g_Trans g13 (g_Trans g1' g12))), a_Star.
  repeat split.
  + simpl. rewrite <- open_co_erase_tm2 with (g := g_Triv). auto.
  + simpl. rewrite <- open_co_erase_tm2 with (g := g_Triv). auto.
  + eapply An_CPiSnd; eauto. rewrite erase_dom. auto.
    rewrite erase_dom. auto.
  + pick fresh x1 for (L \u fv_co_co_tm B1').
    rewrite (co_subst_co_tm_intro x1).
    replace a_Star with (co_subst_co_tm (g_Trans g3 (g_Trans g1 g8)) x1 a_Star).
    eapply AnnTyping_co_subst.
    eauto.
    eauto.
    simpl. auto. auto.
  + pick fresh x1 for (L0 \u fv_co_co_tm B2').
    rewrite (co_subst_co_tm_intro x1).
    replace a_Star with (co_subst_co_tm (g_Trans g13 (g_Trans g1' g12)) x1 a_Star).
    eapply AnnTyping_co_subst.
    eapply H16; eauto 1.
    eauto 1.
    simpl. auto.
    auto.
- (* Cast *)
  clear i. clear d.
  destruct (H G0 H1 H2) as [g [a0' [b0' [A0' [EA [EB [S2 [DE [T1 _]]]]]]]]]. clear H.
  destruct (H0 G0 H1 H2) as [g1 [phi' [phi2' [EP1 [EP2 IP]]]]]. clear H0.
  destruct (AnnIso_regularity IP) as [WFF1 WFF2].
  inversion WFF1. inversion WFF2. subst.
  move: (AnnTyping_regularity H) => ?.
  move: (AnnTyping_regularity H0) => ?.
  move: (AnnTyping_regularity H6) => ?.
  move: (AnnTyping_regularity H7) => ?.
  assert (EA0A1 : AnnDefEq G0 D (g_IsoSnd g1) A0 A1).
  {  eapply An_IsoSnd. eauto. }
  assert (exists g, AnnDefEq G0 D g B B0).
  { eapply (erasure_AnnDefEq EA0A1); eauto 1. }
  destruct H1 as [g2 EBB0].

  destruct (AnnDefEq_regularity DE) as [C [D1 [g3 [TC [TD CD]]]]].
  simpl in EP1. inversion EP1.
  simpl in EP2. inversion EP2. subst. clear EP2. clear EP1.
  resolve_unique_nosubst.


  assert (exists g, AnnDefEq G0 D g a0 a0').
  { eexists.
    eapply An_EraseEq. eauto. eauto. eauto.
    eapply An_EraseEq. eapply AnnTyping_regularity. eauto.
    eapply AnnTyping_regularity. eauto. eauto.
    eapply An_Refl. eauto. }
  destruct H1 as [g4 Ea0a0'].

  assert (exists g, AnnDefEq G0 D g B0 A1).
  { eexists.
    eapply An_EraseEq. eauto. eapply AnnTyping_regularity. eauto. eauto.
    eapply An_Refl. eauto. }
  destruct H1 as [g5 EB0A1].

  assert (exists g, AnnDefEq G0 D g A0 A0').
  { eexists.
    eapply An_EraseEq. eauto. eapply AnnTyping_regularity. eauto. eauto.
    eauto. }
  destruct H1 as [g6 EA0A0'].

  move: (An_Trans2 (An_Trans2 EB0A1 (An_Sym2 EA0A1)) EA0A0') => EB0A0'.
  move: (An_Trans2 (AnnDefEq_weaken_available EB0A0') CD) => EB0D1.
  move: (An_Trans2 (AnnDefEq_weaken_available EBB0) EB0D1) => EBD1.

  assert (exists g, AnnDefEq G0 D g b0 b0').
  { eexists.
    eapply An_EraseEq. eauto. eauto. eauto. eauto.
  }
  destruct H1 as [g7 Eb0b0'].
  (* assert (exists g, AnnIso G0 D g (Eq a0 b0 A0) (Eq a1 (a_Conv b1 g5) A0)) *)

  eexists. exists a1, (a_Conv b1 g5), A1.
  repeat split.
  eapply An_Trans2 with (a1 := b1).
  eapply (An_Cast _ _ _ _ _ _ _ _ _ _ _ IP); eauto 1.
  eapply An_EraseEq. eauto 1.
  eapply An_Conv with (B := A1); eauto 1.
  eapply AnnDefEq_weaken_available; eauto 1.
  simpl. auto.
  eapply AnnDefEq_weaken_available; eauto 1.
  eauto 1.
  eapply An_Conv with (B := A1); eauto 1.
  eapply AnnDefEq_weaken_available; eauto 1.
  Unshelve.
  Focus 2.
  eapply (An_Trans2 (An_Trans2 Ea0a0' DE) (An_Sym2 Eb0b0')).
- (* EqConv *)
  clear d. clear d0.
  destruct (H G0 H1 H2) as [g [a0' [b0' [A0' [EA [EB [S2 [DE [T1 U1]]]]]]]]]. clear H.
  destruct (H0 G0 H1 H2) as [g1 [A' [B' [S' [EP1 [EP2 [ES [DE2 [T2 U2]]]]]]]]]. clear H0.
  subst. rewrite -erase_dom in DE2.

  assert (exists g, AnnDefEq G0 D g A0' A').
  { eexists.
    eapply An_EraseEq. eauto. eapply AnnTyping_regularity. eauto. eauto.
    eauto.  eapply An_EraseEq.
    eapply An_Star. eauto 1. eapply AnnTyping_regularity. eauto.
    autorewcs. eauto 1.
    eapply An_Refl. eauto. }
  destruct H as [g2 EA0'A'].

  move: (An_Trans2 (AnnDefEq_weaken_available EA0'A') DE2) => EA0'B'.
  move: (AnnTyping_regularity T1) => TA0'.
  destruct (AnnDefEq_invertb EA0'B') as (S'' & B'' & g3 & TS & TB & EB & DB'B'').
  resolve_unique_nosubst.

  move: (An_Trans2 EA0'B' DB'B'') => EA0'B''.
  assert (exists g, AnnDefEq G0 D g (a_Conv a0' (g_Trans (g_Trans g2 g1) g3)) a0').
  { eexists. eapply An_EraseEq; eauto 1.
    eapply An_Conv; eauto 1. eapply An_Sym2. eauto.
  }
  destruct H as [g4 Ea0'].
  eexists. exists (a_Conv a0' (g_Trans (g_Trans g2 g1) g3)),
              (a_Conv b0' (g_Trans (g_Trans g2 g1) g3)), B''.
  repeat split; auto.
  eapply An_Trans2 with (a1 := a0'); eauto 1.
  eapply An_Trans2 with (a1 := b0'); eauto 1.
  eapply An_EraseEq; eauto 1. eapply An_Conv; eauto 1.
  eapply An_Conv; eauto 1.
  eapply An_Conv; eauto 1.
- clear i.
  destruct (H G0 H0 H1) as [g1 [phi' [phi2' [EP1 [EP2 IP]]]]]. clear H.
  destruct (AnnIso_regularity IP) as [WFF1 WFF2].
  inversion WFF1. inversion WFF2. subst.
  move: (AnnTyping_regularity H) => ?.
  move: (AnnTyping_regularity H6) => ?.
  simpl in EP1. inversion EP1.
  simpl in EP2. inversion EP2. subst. clear EP2. clear EP1.

  eexists. exists A0, A1, a_Star.
  repeat split; eauto 1.
  eapply An_IsoSnd. eauto.
Qed.









End erase.
