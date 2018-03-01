Require Import FcEtt.imports.
Require Import FcEtt.ett_ott.

Require Import FcEtt.ett_inf.
Require Import FcEtt.ett_par.

Require Import FcEtt.ett_ind.

Require Import FcEtt.ext_wf.

Require Import FcEtt.ext_red_one.

Require Import FcEtt.tactics.

Require Export FcEtt.ext_invert.

Require Export FcEtt.ext_red_one.
Require Export FcEtt.ext_weak.
Require Export FcEtt.ext_subst.
Require Import FcEtt.ett_erased.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


Lemma Beta_preservation : forall a b R, Beta a b R -> 
                                   forall G A, Typing G a A R -> Typing G b A R.
Proof.
  intros a b R B. destruct B; intros G A0 TH.
  - have CT: Ctx G by eauto.
    have RA: Typing G A0 a_Star Rep by eauto using Typing_regularity.
    destruct rho.
    + destruct (invert_a_App_Rel TH) as (A & B & TB & DE & h).
      destruct (invert_a_UAbs TB) as (A1 & B1 & DE2 & [L TB1] & TA1 ).
      eapply E_Conv with (A := (open_tm_wrt_tm B1 b)); eauto 2.
      pick fresh x.
      move: (TB1 x ltac:(auto)) =>  [T1 [T2 RC]].
      rewrite (tm_subst_tm_tm_intro x v); eauto 2. 
      rewrite (tm_subst_tm_tm_intro x B1); eauto 2.
      
      eapply Typing_tm_subst with (A:=A1); eauto 2.
      eapply E_Conv with (A := A); eauto 2.
      eapply E_Sym.
      eapply E_Trans with (a1:= open_tm_wrt_tm B b); eauto 3.

    + destruct (invert_a_App_Irrel TH) as (A & B & b0 & Tb & Tb2 & EQ & DE ).
      subst.
      destruct (invert_a_UAbs Tb) as (A1 & B1 & DE2 & [L TB1] & TA1 ).
      eapply E_Conv with (A := (open_tm_wrt_tm B1 b0)); eauto 2.
      pick fresh x.
      move: (TB1 x ltac:(auto)) =>  [T1 [T2 RC]].
      inversion RC. subst.
      rewrite (tm_subst_tm_tm_intro x v); eauto 2.
      rewrite (tm_subst_tm_tm_intro x B1); eauto 2.
      rewrite (tm_subst_tm_tm_fresh_eq _ _ _ H1).
      rewrite - (tm_subst_tm_tm_fresh_eq _ b0 x H1).
      eapply Typing_tm_subst with (A:=A1); eauto 2.
      eapply E_Conv with (A:=A); eauto using E_PiFst.
      eapply E_Sym.
      eapply E_Trans with (a1 := open_tm_wrt_tm B b0). auto.
      eapply E_PiSnd; eauto using E_Refl.
   - have CT: Ctx G by eauto.
     have RA: Typing G A0 a_Star Rep by eauto using Typing_regularity.
     destruct (invert_a_CApp TH) as (eq & a1 & b1 & A1 & R1 & B1 & h0 & h1 & h2 ).
     destruct (invert_a_UCAbs h0) as (a2 & b2 & A2 & R3 & B2 & h4 & h5 & [L h6] ).
     pick fresh c.
     move: (h6 c ltac:(auto)) => [T1 T2].
     have? : DefEq G (dom G) a2 b2 A2 R3. 
     eauto using E_CPiFst, E_Cast.
     eapply E_Conv with (A:= (open_tm_wrt_co B2 g_Triv)); eauto 2.
     rewrite (co_subst_co_tm_intro c a'); eauto.
     rewrite (co_subst_co_tm_intro c B2); eauto.
     eapply Typing_co_subst; eauto.
     eapply E_Sym.
     eapply E_Trans with (a1 := open_tm_wrt_co B1 g_Triv). auto.
     eapply E_CPiSnd; eauto 2.
   - destruct (invert_a_Fam TH) as (b & B & R2 & h1 & h2 & h3).
     assert (Ax a A R = Ax b B R2). eapply binds_unique; eauto using uniq_toplevel.
     inversion H1. subst. clear H1.
     eapply E_Conv with (A := B).
     eapply toplevel_closed in h2.
     eapply Typing_weakening with (F:=nil)(G:=nil)(E:=G) in h2; simpl_env in *; auto.
     eapply E_SubRole; eauto 1.
     eauto 2.
     eapply E_Sym. eauto.
     eapply Typing_regularity. 
     eauto.
   - dependent induction TH; eauto.
   - dependent induction TH; eauto.
     Unshelve. exact (dom G). exact (dom G).
Qed.


Lemma E_Beta2 :  ∀ (G : context) (D : available_props) (a1 a2 B : tm) R,
       Typing G a1 B R → Beta a1 a2 R → DefEq G D a1 a2 B R.
Proof.
  intros; eapply E_Beta; eauto.
  eapply Beta_preservation; eauto.
Qed.

Lemma Par_fv_preservation: forall W x a b R, Par W a b R ->
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
    have: x `notin` fv_tm_tm_tm (open_tm_wrt_co B (g_Var_f c0)) => h0.
    apply fv_tm_tm_tm_open_tm_wrt_co_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    simpl in h0.
    fsetdec.
    have h2: x `notin` fv_tm_tm_tm (open_tm_wrt_co B' (g_Var_f c0)). eauto.
    move: (fv_tm_tm_tm_open_tm_wrt_co_lower B' (g_Var_f c0)) => h3.
    have h4: x `notin` fv_tm_tm_tm a'. fsetdec.
    move => h1.
    apply AtomSetFacts.union_iff in h1.
    case: h1 => h1; eauto.
    apply AtomSetFacts.union_iff in h1.
    case: h1 => h1; eauto.
    fsetdec.
  - apply toplevel_closed in H.
    move: (Typing_context_fv H) => ?. split_hyp.
    simpl in *.
    fsetdec.
  - eauto.
  - eauto.
  - eauto.
Qed.

Lemma reduction_in_Par : forall a a' R, reduction_in_one a a' R ->
                                   forall W, erased_tm W a R -> Par W a a' R.
Proof.
  induction 1; intros.
  all: try solve [inversion H1; subst; eauto].
  all: try solve [inversion H0; subst; eauto].
  - inversion H1.
    pick fresh x and apply Par_Abs.
    eapply H0; eauto 2.
  - inversion H2; subst.
    eauto.
  - inversion H; subst.
    + inversion H0; subst.
      eapply Par_Beta; eauto.
    + inversion H0; subst.
      eapply Par_CBeta; eauto.
    + inversion H0; subst.
      eapply Par_Axiom; eauto.
    + inversion H0; subst. eapply Par_PatternTrue; eauto.
    + inversion H0; subst. eapply Par_PatternFalse; eauto.
Qed.




Lemma reduction_in_one_fv_preservation: forall x a b R W , reduction_in_one a b R -> erased_tm W a R ->
                                        x `notin` fv_tm_tm_tm a ->
                                        x `notin` fv_tm_tm_tm b.
Proof.
  intros.
  eapply Par_fv_preservation; eauto.
  eapply reduction_in_Par; eauto.
Qed.

Lemma reduction_rhocheck : forall a a' rho x R W, 
    reduction_in_one a a' R -> erased_tm W a R -> RhoCheck rho x a -> RhoCheck rho x a'.
Proof.
  intros.
  inversion H1; subst.
  -  eauto using reduction_in_one_lc.
  -  eauto using reduction_in_one_fv_preservation.
Qed.

Lemma reduction_preservation : forall a a' R, reduction_in_one a a' R -> forall G A, 
      Typing G a A R -> Typing G a' A R.
Proof.
  (* TODO: clean and make more robust *)
  move=> a a' R r.
  induction r.
  all: move=> G A_ tpga.
  - move: (Typing_regularity tpga) => h0.
    autoinv.
    eapply E_Conv with (A := (a_Pi Irrel x R x0)); auto.
    pick fresh y and apply E_Abs; auto.
    apply_first_hyp; auto.
    apply H2. auto. eauto.
    eapply reduction_rhocheck; eauto.
    eapply Typing_erased; eauto.
    eapply H2. auto.
    eapply H2. auto. eauto.
  - move: (Typing_regularity tpga) => h0. 
    autoinv; subst.
    eapply E_Conv with (A := (open_tm_wrt_tm x0 b)); auto.
    eapply E_App; eauto. eauto.
    eapply E_Conv with (A := (open_tm_wrt_tm x0 x1)); auto.
    eapply E_IApp; eauto. eauto.
  - move: (Typing_regularity tpga) => h0. 
    autoinv; subst.
    eapply E_Conv with (A:= (open_tm_wrt_co x3 g_Triv)); auto.
    eapply E_CApp; eauto. eauto.
  - apply invert_a_Pattern in tpga.
    inversion tpga as [A [B0 [a0 [A0 [R1 [P1 [P2 [P3 [P4 P5]]]]]]]]].
    eapply E_Pat. eauto. eauto. eapply E_Conv. eauto. eauto.
    eapply DefEqIso_regularity. eapply E_Sym. eauto.
    eapply E_Conv. eauto. eauto.
    eapply DefEqIso_regularity. eapply E_Sym. eauto.
  - eapply Beta_preservation; eauto.
Qed.

