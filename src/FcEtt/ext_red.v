Require Import FcEtt.imports.
Require Import FcEtt.ett_ott.

Require Import FcEtt.ett_inf.
Require Import FcEtt.ett_par.

Require Import FcEtt.ett_ind.

Require Import FcEtt.ext_wf.

Require Import FcEtt.ext_red_one.

Require Import FcEtt.tactics.

Require Export FcEtt.ext_invert.

Require Export FcEtt.ext_subst.
Require Export FcEtt.ext_weak.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


Lemma Beta_preservation : forall a b R, Beta a b R  -> forall G A, Typing G a A R -> Typing G b A R.
Proof.
  intros a b R B. destruct B; intros G A0 TH.
  - (* AppAbs *)
    have CT: Ctx G by eauto.
    have RA: Typing G A0 a_Star R1 by eauto using Typing_regularity.
    destruct rho.
    + destruct (invert_a_App_Rel TH) as (A & B & R2 & TB & Tb & DE & SR1).
      destruct (invert_a_UAbs TB) as (A1 & B1 & DE2 & [L TB1] & TA1).
      eapply E_Conv with (A := (open_tm_wrt_tm B1 b)); eauto 2.
      pick fresh x.
      move: (TB1 x ltac:(auto)) =>  [T1 [T2 RC]].
      rewrite (tm_subst_tm_tm_intro x v); eauto.
      rewrite (tm_subst_tm_tm_intro x B1); eauto.
      eapply Typing_tm_subst with (A:=A1); eauto 2.
      eapply E_Conv with (A := A); eauto 2 using E_PiFst.
      eapply E_Trans with (a1:= open_tm_wrt_tm B b); eauto 1.
      eapply E_Sub with (R1:=R2); eauto 1.
      eapply E_Sym.
      eapply E_PiSnd; eauto 1.
      eapply E_Refl; auto.
      eapply E_Sym. auto.
    + destruct (invert_a_App_Irrel TH) as (A & B & b0 & R2 & Tb & Tb2 & DE & SR1).
      destruct (invert_a_UAbs Tb) as (A1 & B1 & DE2 & [L TB1] & TA1 ).
      eapply E_Conv with (A := (open_tm_wrt_tm B1 b0)); eauto 2.
      pick fresh x.
      move: (TB1 x ltac:(auto)) =>  [T1 [T2 RC]].
      inversion RC. subst.
      rewrite (tm_subst_tm_tm_intro x v); eauto.
      rewrite (tm_subst_tm_tm_intro x B1); eauto.
      rewrite (tm_subst_tm_tm_fresh_eq _ _ _ H1).
      rewrite - (tm_subst_tm_tm_fresh_eq _ b0 x H1).
      eapply Typing_tm_subst with (A:=A1); eauto 2.
      eapply E_Conv with (A:=A); eauto using E_PiFst.
      eapply E_Sym.
      eapply E_Trans with (a1 := open_tm_wrt_tm B b0). auto.
      eapply E_PiSnd; eauto using E_Refl.
   - (* CAppCAbs *)
     have CT: Ctx G by eauto.
     have RA: Typing G A0 a_Star R by eauto using Typing_regularity.
     destruct (invert_a_CApp TH) as (eq & a1 & b1 & A1 & R1 & B1 & R2 & h0 & h1 & h2 & h3).
     destruct (invert_a_UCAbs h0) as (a2 & b2 & A2 & R3 & B2 & R4 & h4 & h5 & [L h6] & h7).
     pick fresh c.
     move: (h6 c ltac:(auto)) => [T1 T2].
     have? : DefEq G (dom G) a2 b2 A2 R3. 
     eapply E_Cast. eapply h1.
     eapply E_CPiFst.
     eauto.
     eapply E_Conv with (A:= (open_tm_wrt_co B2 g_Triv)); eauto 2.
     rewrite (co_subst_co_tm_intro c a'); eauto.
     rewrite (co_subst_co_tm_intro c B2); eauto.
     eapply Typing_co_subst; eauto.
     eapply E_Sym.
     eapply E_Trans with (a1 := open_tm_wrt_co B1 g_Triv). auto.
     eapply E_CPiSnd; eauto 2.
   - (* Axiom *)
     destruct (invert_a_Fam TH) as (b & B & R1 & h0 & h1 & h2).
     assert (Ax a A R = Ax b B R1). eapply binds_unique; eauto using uniq_toplevel.
     inversion H0. subst.
     eapply E_Conv with (A := B).
     eapply toplevel_closed in h1.
     eapply Typing_weakening with (F:=nil)(G:=nil)(E:=G) in h1.
     simpl_env in h1. eauto.
     auto. simpl_env. eauto.
     eapply E_Sym. eauto.
     move: (DefEq_regularity h0) => h4.
     inversion h4.
     auto.
     Unshelve. exact (dom G). exact (dom G).
   - (* Drop *)
     destruct (invert_a_Conv2 TH) as (b & h1 & h).
     destruct R; destruct R1.
     + eapply E_Conv; eauto 2.
       eapply Typing_regularity; eauto.
     + apply rep_nsub_nom in H0. contradiction.
     + eapply E_Conv; eauto 2.
       eapply E_Sub; eauto 1.
       eapply E_Sym; eauto 1.
       eapply Typing_regularity; eauto.
     + eapply E_Conv; eauto 2.
       eapply Typing_regularity; eauto.
   - (* Combine *)
     destruct (invert_a_Conv2 TH) as (b & h1 & h).
     destruct (invert_a_Conv2 h1) as (b0 & h2 & h3).
     eapply E_TyCast; eauto 1.
     eapply E_Sym.
     eapply E_Trans; eauto 1.
     eapply Typing_regularity; eauto.
   - (* Push *)
     destruct rho.
     * destruct (invert_a_App_Rel TH) as (A2 & B2 & R2 & h). split_hyp.
       destruct (invert_a_Conv2 H1) as (C & h2 & h3).
       assert (R2 = Nom). { destruct R2. auto.
                            apply rep_nsub_nom in H4. contradiction. }
       subst R2. clear H4.
       inversion H0. subst. inversion H4. subst a.
       eapply E_TyCast; eauto 2 using Typing_regularity. subst a.
       eapply E_App; eauto 1.
       
SearchAbout Typing a_Conv.

Lemma invert_a_Conv :  
  ∀ (G : context) (a A : tm) (R1 R2 : role), Typing G (a_Conv a R1 g_Triv) A R2
                                             → ∃ B : tm, Typing G a B R2
                                               ∧ DefEq G (dom G) A B a_Star R1.
Print E_Conv.
Proof.
  intros.
  dependent induction H.


       destruct (invert_a_Conv2 h1) as (B' & h2 & h).
       eapply E_TyCast. 3 : { eapply Typing_regularity; eauto. }
       eapply E_App. eapply E_Conv. eauto 1.
       eapply E_Sym. eapply E_Sub; eauto 1.

eapply E_SubRole. eauto 1. eauto 1.
       eapply E_Sym.

       eapply E_TyCast with (A1 := (open_tm_wrt_tm B2 (a_Conv b R g_Triv))).
Admitted.


Check invert_a_Conv.


Lemma E_Beta2 :  ∀ (G : context) (D : available_props) (a1 a2 B : tm) R,
       Typing G a1 B R → Beta a1 a2 → DefEq G D a1 a2 B R.
Proof.
  intros; eapply E_Beta; eauto.
  eapply Beta_preservation; eauto.
Qed.

Lemma Par_fv_preservation: forall G D x a b, Par G D a b ->
                                        x `notin` fv_tm_tm_tm a ->
                                        x `notin` fv_tm_tm_tm b.
Proof.
  intros.
  induction H; eauto 2; simpl.
  all: simpl in H0.
  all: try solve [move => h0; apply AtomSetFacts.union_iff in h0; case: h0 => h0; eauto; apply IHreduction_in_one; auto].
  - simpl in *.
    have: x `notin` fv_tm_tm_tm (open_tm_wrt_tm a' b') => h0.
    apply fv_tm_tm_tm_open_tm_wrt_tm_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    fsetdec_fast.
    fsetdec_fast.
    auto.
  - auto.
  - have: x `notin` fv_tm_tm_tm (open_tm_wrt_co a' g_Triv) => h0.
    apply fv_tm_tm_tm_open_tm_wrt_co_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    fsetdec.
    auto.
  - auto.
  - pick fresh x0.
    assert (Fl : x0 `notin` L). auto.
    assert (Fa : x `notin` fv_tm_tm_tm (open_tm_wrt_tm a (a_Var_f x0))).
    rewrite fv_tm_tm_tm_open_tm_wrt_tm_upper. auto.
    move: (H1 x0 Fl Fa) => h0.
    rewrite fv_tm_tm_tm_open_tm_wrt_tm_lower. eauto.
  - pick fresh x0.
    have na': x `notin` fv_tm_tm_tm A'. eauto.
    have nb: x `notin` fv_tm_tm_tm (open_tm_wrt_tm B (a_Var_f x0)).
    rewrite fv_tm_tm_tm_open_tm_wrt_tm_upper. eauto.
    have nob': x `notin` fv_tm_tm_tm (open_tm_wrt_tm B' (a_Var_f x0)). eauto.
    have nb': x `notin` fv_tm_tm_tm B'.
    rewrite fv_tm_tm_tm_open_tm_wrt_tm_lower. eauto.
    eauto.
  - pick_fresh c0.
    have: x `notin` fv_tm_tm_tm (open_tm_wrt_co a (g_Var_f c0)) => h0.
    apply fv_tm_tm_tm_open_tm_wrt_co_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    simpl in h0.
    fsetdec.
    have K:= H1 c0 ltac:(auto) h0.
    move => h1.
    apply K. auto.
    apply fv_tm_tm_tm_open_tm_wrt_co_lower; auto.
  - pick fresh c0 for L.
    have: x `notin` fv_tm_tm_tm (open_tm_wrt_co a (g_Var_f c0)) => h0.
    apply fv_tm_tm_tm_open_tm_wrt_co_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    simpl in h0.
    fsetdec.
    have h2: x `notin` fv_tm_tm_tm (open_tm_wrt_co a' (g_Var_f c0)). eauto.
    move: (fv_tm_tm_tm_open_tm_wrt_co_lower a' (g_Var_f c0)) => h3.
    have h4: x `notin` fv_tm_tm_tm a'. fsetdec.

    move => h1.
    apply AtomSetFacts.union_iff in h1.
    case: h1 => h1; eauto.
    apply AtomSetFacts.union_iff in h1.
    case: h1 => h1; eauto.
    fsetdec.
    fsetdec.
  - apply toplevel_closed in H.
    move: (Typing_context_fv H) => ?. split_hyp.
    simpl in *.
    fsetdec.
Qed.


Lemma reduction_in_Par : forall a a', reduction_in_one a a' -> forall G D, Par G D a a'.
Proof.
  induction 1; intros; eauto.
  - eapply Par_Beta; eauto using Value_lc.
Qed.




Lemma reduction_in_one_fv_preservation: forall x a b, reduction_in_one a b ->
                                        x `notin` fv_tm_tm_tm a ->
                                        x `notin` fv_tm_tm_tm b.
Proof.
  intros.
  eapply Par_fv_preservation; eauto.
  eapply reduction_in_Par; eauto.
  Unshelve. exact nil. exact {}.
Qed.

Lemma reduction_rhocheck : forall a a' rho x, reduction_in_one a a' -> RhoCheck rho x a -> RhoCheck rho x a'.
Proof.
  move=> a a' [] x Red RC.
  - inversion RC.  eauto using reduction_in_one_lc.
  - inversion RC.  eauto using reduction_in_one_fv_preservation.
Qed.

Lemma reduction_preservation : forall a a', reduction_in_one a a' -> forall G A R, Typing G a A R -> Typing G a' A R.
Proof.
  (* TODO: clean and make more robust *)
  move=> a a' r.
  induction r.
  all: move=> G A_ R' tpga.
  - depind tpga; try eauto.
    + eapply E_Abs with (L := L `union` L0); try eassumption.
      all: move=> x xLL0.
      all: autofresh_fixed x.
      all: eauto using reduction_rhocheck.
  - depind tpga; subst; eauto.
  - depind tpga; subst; eauto.
  - destruct rho.
    + apply invert_a_App_Rel in tpga.
      pcess_hyps.
      apply invert_a_UAbs in H1. pcess_hyps.
      autofresh. pcess_hyps.
      move: (E_PiFst _ _ _ _ _ _ _ _ _ H1) => xx1.
      eapply E_Conv; try eapply (E_Sym _ _ _ _ _ _ H3).
      rewrite  (tm_subst_tm_tm_intro x5); try fsetdec_fast.
      rewrite (tm_subst_tm_tm_intro x5 x0); try fsetdec_fast.
      eapply Typing_tm_subst.
      have x5_refl : DefEq ([(x5, Tm x2 R)] ++ G) (dom G) (a_Var_f x5) (a_Var_f x5) x R.
      {
        eapply E_Refl; eapply E_Conv.
        - eauto.
        - eapply E_Sym in xx1.
          eapply DefEq_weaken_available.
          rewrite <- (app_nil_l [(x5, Tm x2 R)]).
          rewrite app_assoc.
          eapply DefEq_weakening; try reflexivity.
          + rewrite app_nil_l. eassumption.
          + simpl. eauto.
        - apply DefEq_regularity in xx1.
          apply PropWff_regularity in xx1.
          destruct xx1.
          rewrite <- (app_nil_l [(x5, Tm x2 R)]).
          rewrite app_assoc.
          eapply Typing_weakening; eauto.
      }
      have x5G: (Ctx (nil ++ [(x5, Tm x2 R)] ++ G)) by eauto.
      move: (DefEq_weakening H1 [(x5, Tm x2 R)] nil G eq_refl x5G) => H1w.
      rewrite app_nil_l in H1w.
      move: (E_PiSnd _ _ _ _ _ _ _ _ _ _ _ H1w x5_refl) => x0x2.
      eapply E_Conv.
      * eapply E_SubRole with (R1 := x1); auto. eapply H5.
      * eapply DefEq_weaken_available.
        eapply E_Sub with (R1 := x1); auto.
        eapply (E_Sym _ _ _ _ _ _ x0x2).
      * apply DefEq_regularity in x0x2.
        eapply E_SubRole with (R1 := x1); auto.
        by inversion x0x2.
      * eauto.
      * (* TODO: autoreg tactic (applies regularity automatically) *)
        apply DefEq_regularity in H3.
        by inversion H3.

    + apply invert_a_App_Irrel in tpga.
      pcess_hyps.
      apply invert_a_UAbs in H1; pcess_hyps.
      autofresh. pcess_hyps. inversion H9.
      move: (E_PiFst _ _ _ _ _ _ _ _ _ H1) => xx2.
      eapply E_Conv; try eapply (E_Sym _ _ _ _ _ _ H3).
      rewrite  (tm_subst_tm_tm_intro x6); try fsetdec_fast.
      rewrite tm_subst_tm_tm_fresh_eq; try done.
      rewrite -(tm_subst_tm_tm_fresh_eq (open_tm_wrt_tm v (a_Var_f x6)) x1 x6); try done.
      rewrite (tm_subst_tm_tm_intro x6 x0); try fsetdec_fast.
      eapply Typing_tm_subst.
      have x6_refl : DefEq ([(x6, Tm x3 R)] ++ G) (dom G) (a_Var_f x6) (a_Var_f x6) x R.
      {
        eapply E_Refl; eapply E_Conv.
        - eauto.
        - eapply E_Sym in xx2.
          eapply DefEq_weaken_available.
          rewrite <- (app_nil_l [(x6, Tm x3 R)]).
          rewrite app_assoc.
          eapply DefEq_weakening; try reflexivity.
          + rewrite app_nil_l. eassumption.
          + simpl. eauto.
        - apply DefEq_regularity in xx2.
          apply PropWff_regularity in xx2.
          destruct xx2.
          rewrite <- (app_nil_l [(x6, Tm x3 R)]).
          rewrite app_assoc.
          eapply Typing_weakening; eauto.
      }
      have x6G: (Ctx (nil ++ [(x6, Tm x3 R)] ++ G)) by eauto.
      move: (DefEq_weakening H1 [(x6, Tm x3 R)] nil G eq_refl x6G) => H1w.
      rewrite app_nil_l in H1w.
      move: (E_PiSnd _ _ _ _ _ _ _ _ _ _ _ H1w x6_refl) => x0x3.
      eapply E_Conv.
      * eapply E_SubRole with (R1 := x2); auto.
        eapply H5.
      * eapply DefEq_weaken_available.
        eapply E_Sub with (R1 := x2); auto.
        eapply (E_Sym _ _ _ _ _ _ x0x3).
      * apply DefEq_regularity in x0x3.
        eapply E_SubRole with (R1 := x2); auto.
        by inversion x0x3.
      * eauto.
      * apply DefEq_regularity in H3.
        by inversion H3.


  - apply invert_a_CApp in tpga; pcess_hyps.
    apply invert_a_UCAbs in H1; pcess_hyps.
    eapply E_Conv; try eapply (E_Sym _ _ _ _ _ H2). (* TODO: declare E_Sym's (and others') arguments implicit *)
    autofresh; pcess_hyps.
    move: (E_CPiFst _ _ _ _ _ _ _ H1) => iso.
    move: (E_Cast _ _ _ _ _ _ _ _ _ _ H2 iso) => x34.
    move: (E_CPiSnd _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 x34) => x26.
    pose (x27 := E_Sub _ _ _ _ _ _ _ x26 H4).
    eapply E_Conv; try eapply (E_Sym _ _ _ _ _ _ x27).
    all: try (apply DefEq_regularity in H3; inversion H3; done).
    rewrite  (co_subst_co_tm_intro x12); try fsetdec_fast.
    rewrite (co_subst_co_tm_intro x12 x9); try fsetdec_fast.
    eapply Typing_co_subst.
    all: eauto.

  - apply invert_a_Fam in tpga; pcess_hyps.
    move: (binds_unique _ _ _ _ _ H H1 uniq_toplevel). inversion 1. subst x0 x.
    apply toplevel_closed in H.
    eapply E_Sym in H0.
    move: (DefEq_regularity H0) => reg; inversion reg. subst.
    eapply Typing_Ctx in H9.
    eapply E_Conv; eauto.
    move: (Typing_weakening H G nil nil eq_refl).
    rewrite app_nil_l app_nil_r. intros.
    eapply E_SubRole with (R1 := x1); auto.
Qed.
