Require Import FcEtt.imports.
Require Import FcEtt.tactics.

Require Import FcEtt.ett_ott.

Require Import FcEtt.ett_inf.
Require Import FcEtt.ett_ind.
(*
Require Import FcEtt.ett_par.
*)


Require Import FcEtt.ext_wf.
Require Export FcEtt.ext_invert.
Require Export FcEtt.ext_weak.
Require Export FcEtt.ext_subst.
Require Import FcEtt.ett_roleing.

Require Import FcEtt.param.

Require Export FcEtt.ext_red_one.
Require Import FcEtt.ett_match.
Require Import FcEtt.pattern.

Require Import FcEtt.notations.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


(* FIXME: temporary *)
Generalizable All Variables.

(******** FIXME: stuff that should be removed/improved/proved somewhere else/etc ********)
Lemma where_is_this : `{
  DefEq Γ D (a_Pi rho1 A1 B1) (a_Pi rho2 A2 B2) K R →
  rho1 = rho2
}.
Proof.
Admitted.

Notation PatCtxTrim Γ p :=
  (exists Ω F PiB B, PatternContexts Ω Γ F PiB p B).


(* Readability notations *)
Notation "'ArgRel' a" := (pattern_arg_Rel a _) (at level 50). (* FIXME: level *)
Notation "'ArgIrr' a" := (pattern_arg_Irr a _) (at level 50). (* FIXME: level *)
Notation "'ArgCoe' a" := (pattern_arg_Coe a _) (at level 50). (* FIXME: level *)


(******** Internal relations used only for proving ********)

(* Represents that G |- A = "PiB opened with args" *)
(* Note: technically, PiB is not just a telescope - it also stores the
   return type. We nevertheless use "telescope" in the naming *)
Inductive chain_open_telescope_deq : context → tm → tm → pattern_args → Prop :=
  | cotd_base : `{Typing Γ A a_Star →
                  chain_open_telescope_deq Γ A A []}

  | cotd_eq   : `{chain_open_telescope_deq Γ A B args →
                  DefEq Γ (dom Γ) A C a_Star R →
                  chain_open_telescope_deq Γ C B args}

(* FIXME: not checking the role here *)
  | cotd_rel  : `{chain_open_telescope_deq Γ (a_Pi Rel A' A) B args →
                  Typing Γ a A' →
                  chain_open_telescope_deq Γ (open_tm_wrt_tm A a) B (pattern_arg_Rel a R :: args)}

  | cotd_irr  : `{chain_open_telescope_deq Γ (a_Pi Irrel A' A) B args →
                  Typing Γ a A' →
                  chain_open_telescope_deq Γ (open_tm_wrt_tm A a) B (pattern_arg_Irr a_Bullet :: args)}

  | cotd_capp : `{chain_open_telescope_deq Γ (a_CPi (Eq C C' K R) A) B args →
                  DefEq Γ (dom Γ) C C' K R →
                  chain_open_telescope_deq Γ (open_tm_wrt_co A g) B (pattern_arg_Coe g :: args)}
.

Notation "#copd: G |= A == B ^ args" := (chain_open_telescope_deq G A B args) (at level 50). (* TODO: figure out the level(s) *)

Hint Constructors chain_open_telescope_deq.

(* Same than previous relation, except we don't allow the use of internal equality.
   Namely, represents A = "PiB opened with args". The base requirements are also
   weakened (no typing check).
   See above for additional details *)
Inductive chain_open_telescope_partial : context → tm → tm → pattern_args → Prop :=
  | cotp_base : `{chain_open_telescope_partial Γ A A []}

  | cotp_rel  : `{chain_open_telescope_partial Γ (a_Pi Rel A' A) B args →
                  Typing Γ a A' →
                  chain_open_telescope_partial Γ (open_tm_wrt_tm A a) B (pattern_arg_Rel a R :: args)}

  | cotp_irr  : `{chain_open_telescope_partial Γ (a_Pi Irrel A' A) B args →
                  Typing Γ a A' →
                  chain_open_telescope_partial Γ (open_tm_wrt_tm A a) B (pattern_arg_Irr a :: args)}

  | cotp_capp : `{chain_open_telescope_partial Γ (a_CPi (Eq C C' K R) A) B args →
                  chain_open_telescope_partial Γ (open_tm_wrt_co A g) B (pattern_arg_Coe g :: args)}
.

Notation "#cotp: G |= A = B ^ args" := (chain_open_telescope_partial G A B args) (at level 50). (* TODO: figure out the level(s) *)

Hint Constructors chain_open_telescope_partial.

Inductive decompose_subpattern :
  tm → tm → pattern_args → pattern_args → context → context → Prop :=
  | dsp_base : `{decompose_subpattern (a_Fam F) (a_Fam F) nil nil nil nil}

  | dsp_full_rel : `{decompose_subpattern p p args nil Γ nil →
                     PatCtxTrim (x ~ Tm A' ++ Γ') (a_App p (Role R) (a_Var_f x)) →
                     decompose_subpattern (a_App p (Role R) (a_Var_f x)) (a_App p (Role R) (a_Var_f x))
                                          (pattern_arg_Rel (a_Var_f x) R :: args) nil
                                          (x ~ Tm A' ++ Γ) nil}

  | dsp_sub_rel  : `{decompose_subpattern p' p args coargs Γ coΓ →
                     PatCtxTrim (x ~ Tm A' ++ coΓ ++ Γ) (a_App p (Role R) (a_Var_f x)) →
                     decompose_subpattern p' (a_App p (Role R) (a_Var_f x))
                                             args (pattern_arg_Rel (a_Var_f x) R :: coargs)
                                             Γ (x ~ Tm A' ++ coΓ)}
.

(* Simple notation to improve readability *)
Notation "#Subpat:  p'  [ctx:  G - args: a ]   '#of'  p  '#by'  ctx: coG - args: coa" := (decompose_subpattern p' p a coa G coG) (at level 50). (* TODO: figure out the level(s) *)

Hint Constructors decompose_subpattern.


(* Checking the types of a list of arguments
  Typing context, list of arguments, context with the types they need to have *)
Inductive args_proper_type : context → pattern_args → context → Prop :=
  | apt_base : `{args_proper_type Γ [] []}
  | apt_rel : `{
    args_proper_type Γ args Γ' →
    Typing Γ a (subst_args_in_term Γ' args A) →
    args_proper_type Γ (pattern_arg_Rel a R :: args) (x ~ Tm A ++ Γ')}
  (* TODO: irr/coe *)
.

Hint Constructors args_proper_type.



(******** Lemmas about these inductives ********)

Lemma chain_open_telescope_deq_Reg : `{
  chain_open_telescope_deq Γ A B args →
  Typing Γ A a_Star
}.
Proof.
  induction 1; ok; autoreg; ok.
  - eapply invert_a_Pi in IHchain_open_telescope_deq.
    autofwd.
    (* TODO: subst *) admit.
Admitted.

(*
Lemma PatternContexts_chain_open_telescope_partial : `{
  PatternContexts Ω Γ' F PiB p B →
  pat_args_default p = args →
  chain_open_telescope_partial Γ B PiB args
}.
Proof.
  intros until 1. move: args.
  induction H; inversion 1; cbn; subst.
  - eauto.
  - eapply cotp_rel. by eapply IHPatternContexts; try done.
  - admit. (* FIXME: pattern needs to have irr args *) (* eapply cpo_irr. eassumption. *)
  - admit. (* eapply cpo_capp. *)
Admitted.
*)

(* TODO: maybe change this lemma to a more general one, and update the name *)
Lemma chain_open_telescope_deq_fv_1 : `{
  x ∉ dom Γ →
  x ∉ fv_tm_args args →
  chain_open_telescope_deq Γ (a_Pi rho A' A0) B args →
  x ∉ fv_tm_tm_tm A0
}.
Proof.
  (* TODO: ugly proof, improve. Also, the Rel case hasn't been updated in a while,
           it might not be the most direct way to prove it anymore (unsure). *)
  intros until 0.
  move=> fvΓ fvargs h.
  dependent induction h.

  - eapply Typing_context_fv in H.
    cbn in H.
    autofwd.
    move: subset_notin.
    move/(_ _ _ (dom Γ)).
    apply; ok.
  - move: (DefEq_context_fv H) => /=.
    ok.
  - cbn in *.
    move: (f_equal fv_tm_tm_tm x) => /=.
    move=> h'. move: (eq_sym h'). (* FIXME shouldn't need to do this by hand *)
    Import AtomSetProperties.
    move: (@subset_refl (fv_tm_tm_tm (open_tm_wrt_tm A a))) => s.
    move=> eq.
    rewrite <-eq in s at 1.
    move: s.
    move/(union_subset _ ). introfwd.
    move: (fv_tm_tm_tm_open_tm_wrt_tm_upper A a) => ?.
    clear H eq.
    move: IHh.
    move/(_ _ _ _ _ ltac:(eauto) ltac:(eauto) ltac:(reflexivity) ltac:(reflexivity)) => IH.
    ok.

  - admit. (* Irr *)
  - admit. (* Coe *)
Admitted.

(* TODO: generalize this lemma (to all cases, not just Rel) and prove *)
Lemma chain_open_telescope_partial_subst_general : `{
  x `notin` dom Γ →
  x `notin` fv_tm_args args →
  Γ ⊨ a : A →
  chain_open_telescope_partial Γ B PiB (coargs ++ one (pattern_arg_Rel (a_Var_f x) R) ++ args) →
  chain_open_telescope_partial Γ (tm_subst_tm_tm a x B) PiB (coargs ++ (pattern_arg_Rel a R :: args))
}.
Proof.
  intros until 0.
  move => fv fv' tpga h; dependent induction h.

  - destruct coargs; cbn in x; inversion x.

  - move: IHh. ecbn.
Admitted.


Lemma chain_open_telescope_partial_subst_general_rel : `{
  x `notin` dom Γ →
  x `notin` fv_tm_args args →
  Γ ⊨ a : A →
  chain_open_telescope_partial Γ B PiB (coargs ++ one (pattern_arg_Rel (a_Var_f x) R) ++ args) →
  chain_open_telescope_partial Γ (tm_subst_tm_tm a x B) PiB (coargs ++ (pattern_arg_Rel a R :: args))
}.
Proof.
  (* TODO: by specialization of previous lemma (after it gets generalized) *)
Admitted.

Lemma chain_open_telescope_partial_subst_Rel : `{
  x `notin` dom Γ →
  x `notin` fv_tm_args args →
  Γ ⊨ a : A →
  chain_open_telescope_partial Γ B PiB ((pattern_arg_Rel (a_Var_f x) R :: args)) →
  chain_open_telescope_partial Γ (tm_subst_tm_tm a x B) PiB ((pattern_arg_Rel a R :: args))
}.
Proof.
  (* FIXME: old, broken proof. Should be obtained from previous lemma instead *)
  (*
  intros until 0.
  move => fv fv' tpga h; dependent induction h.

  - move: IHh.
    move/(_ tpga _ _ _ fv _ ltac:(reflexivity)) => ih.
    eapply (cpo_eq ih).
    move: (DefEq_context_fv H); introfwd.
    rewrite tm_subst_tm_tm_fresh_eq. { ok. }
    rewrite tm_subst_tm_tm_fresh_eq. { ok. }
    ok.

  - rewrite <- tm_subst_tm_tm_intro; last first.
    {
      eapply chain_open_telescope_deq_fv_1; ok.
    }
    eapply cpo_rel.
    ok.
  *)
Admitted.


Lemma invert_cotd_ArgRel : `{
  chain_open_telescope_deq Γ A PiB (pattern_arg_Rel a2 R :: args) -> 
  Γ ⊨ a1 : a_Pi Rel A2 B2 →
  Γ ⊨ a2 : A2 →
  DefEq Γ (dom Γ) A (open_tm_wrt_tm B2 a2) a_Star Rep →
  chain_open_telescope_deq Γ (a_Pi rho A' B2) PiB args}.
Proof.
Admitted.


Lemma decompose_subpattern_refl : `{
  PatternContexts Ω Γ F PiB p B →
   ∃ args, 
  decompose_subpattern p p args nil Γ nil 
}.
Proof.
  induction 1; ok.
  - econstructor; ok.
    econstructor.
    eassumption.
    eassumption.
  - admit. (* TODO: Irrel *)
  - admit. (* TODO: Coe *)
Admitted.

Lemma decompose_subpattern_pat_head : `{
  decompose_subpattern (a_Fam F) p args coargs Γ coΓ →
  pat_head p = Some F
}.
Proof.
  move => ?????? h.
  dependent induction h; ok.
Qed.

(* FIXME: naming conventions *)
Lemma dsp_patctx_cotp : `{
  decompose_subpattern (a_Fam F) p p'args cop'args ∅ coΓp' →
  PatternContexts Ω' coΓp' F PiB p B →
  chain_open_telescope_partial Γ B PiB cop'args}.
Proof.
  (* TODO *)
Admitted.

Lemma dsp_invert_rel : `{
  decompose_subpattern (a_App a (Role R) (a_Var_f x)) p args coargs Γ coΓ →
  exists args' A Γ',
  args = pattern_arg_Rel (a_Var_f x) R :: args' /\
  Γ = x ~ Tm A ++ Γ' /\
  decompose_subpattern a p args' (coargs ++ [pattern_arg_Rel (a_Var_f x) R]) Γ' (coΓ ++ x ~ Tm A)
}.
Proof.
  (* TODO *)
Admitted.

Lemma decompose_subpattern_fv : `{
  decompose_subpattern p' p args coargs Γ coΓ →
  fv_tm_tm_tm p' [=] dom Γ /\ fv_tm_tm_tm p [=] dom Γ ∪ dom coΓ
}.
Proof.
  induction 1; cbn; ok.
Qed.

Lemma decompose_subpattern_fv_rel : `{
  decompose_subpattern p' (a_App p f (a_Var_f x0)) args coargs Γ (x0 ~ Tm A ++ coΓ) →
  fv_tm_tm_tm p [=] dom Γ ∪ dom coΓ
}.
Proof.
  intros until 0.
  move=> h; dependent induction h.
  eapply decompose_subpattern_fv in h.
  ok.
Qed.


Definition Pattern := ett_ott.Pattern. (* FIXME: a file (ett_match maybe?) is masking Pattern *)

(******** Main lemmas ********)

Lemma invert_cons_ln : `(
  binds F (Ax p b PiB R1 Rs) toplevel →
  PatternContexts Ω' Γ' F PiB p B → (* PiB just stands for B with some quantifiers in front of it *)
  Rename p b p1 b1 ((fv_tm_tm_tm a) ∪ (fv_tm_tm_tm p)) D →
  Γ ⊨ a : A →
  ∀ p',
  tm_pattern_agree a p' →
  SubPat p' p1 →
    chain_open_telescope_deq Γ A PiB (pat_args_default a)
).
Proof.
  intros until 3.
  move=> tpg; autoreg; move: tpg.
  induction 1; last 2 first.

  (* Removing all cases that don't apply - where `a` can't match any pattern *)
  all: try solve [inversion 1].

  all: exactly 6 goals.

  (* Base case (axiom typing) *)
  - inversion 1. subst.
    introfwd.
    cbn.
    move: (SubPat_pat_head H5) => /= h1.
    move: (Rename_pat_head H1) => h4.
    move: (binds_toplevel_pat_head H) => h.
    have eqf: F = F0 by congruence.
    subst.
    move: (binds_unique _ _ _ _ _ H H3 uniq_toplevel).
    injection 1.
    ok.

  (* Relevant app *)
  - inversion 1.
    introfwd; subst.
    autoreg.
    eapply IHtpg1 in H9; first last; try done.
    (* Subpattern *)
    { move: H10.
      clearall.
      move=> h; dependent induction h; try inversion H; ok. }
    (* Renaming hyp *)
    { cbn in H1.
      eapply Rename_subset.
      by eassumption.
      ok. }
    econstructor 3; eassumption.

  (* Irrelevant app *)
  - inversion 1.
    introfwd; subst.
    autoreg.
    eapply IHtpg1 in H7; first last; try done.
    (* Subpattern *)
    { move: H8.
      clearall.
      move=> h; dependent induction h; try inversion H; ok. }
    (* Renaming hyp *)
    { cbn in H1.
      (* rewrite union_empty_r in H1. *) (* FIXME: somehow, this loops..? *)
      eapply Rename_subset.
      by eassumption.
      ok. }
    econstructor 4; eassumption.

  (* Conversion *)
  - introfwd.
    autoreg.
    eapply IHtpg1 in H3; ok.

  (* CApp *)
  - introfwd.
    inversion H3.
    autoreg.
    eapply IHtpg in H6; first last; try done.
    (* Subpattern *)
    { subst.
      move: H4.
      clearall.
      move=> h. dependent induction h; try inversion H; ok. }
    (* Renaming hyp *)
    { cbn in H1.
      (* rewrite union_empty_r in H1. *) (* FIXME: somehow, this loops..? *)
      eapply Rename_subset.
      by eassumption.
      ok. }
    econstructor 5; eassumption.

  (* Absurd case (constant typing - binding both F as an axiom and as a constant) *)
  - introfwd.
    inversion H4; subst. eapply SubPat_pat_head in H5; autofwd. cbn in H5.
    move: (binds_toplevel_pat_head H) => eph2.
    move: (Rename_pat_head ltac:(eassumption)) => eph1.
    have eqF : F = F0 by congruence.
    subst.
    by move: (binds_unique _ _ _ _ _ H H3 uniq_toplevel).
Qed.



(* Warning: here, p is assumed to have already been renamed to avoid variables in a.
   Namely, using the notations of the toplevel theorem, it corresponds to p1, not p *)
Lemma TODO_name : `{
  PatternContexts Ω' Γ' F PiB p B →
  (fv_tm_tm_tm p) ∩ (fv_tm_tm_tm a) [=] empty →
  MatchSubst a p' b b' →
  forall args A p'args cop'args Γp' coΓp',
  Γ' ⊨ b : B →
  Γ ⊨ a : A →
  pat_args_default a = args → (* FIXME: temporarily not enforcing head a = F, is it okay? *)
  (* subpattern p' p → *)
  decompose_subpattern p' p p'args cop'args Γp' coΓp' → 
  Γ' = coΓp' ++ Γp' →
  args_proper_type Γ args Γp' →
    ∃ B',
  chain_open_telescope_partial Γ B' PiB (cop'args ++ args) /\
  (subst_args_in_ctx Γp' args coΓp') ++ Γ ⊨ b' : B'
}.
Proof.
  induction 3; introfwd.

  - cbn in H4. invs H4.
    move: (decompose_subpattern_pat_head H5); introfwd. subst.
    ok.
    + ecbn.
      have ? : Γp' = nil by cbn in H7; inversion H7. subst.
      ecbn in H.
      move: (@dsp_patctx_cotp).
      move: (PatternContexts_pat_head H) => ?.
      have ? : F = F0 by congruence. subst.
      move /(_ _ _ _ _ _ _ _ _ _ H5 H).
      by ecbn.
    + ecbn. admit. (* Weakening *)

  (* Rel *)
  - invs H6; (* CHECK: no need for dependent induction, right? *)
    softclear H6.
    (* eapply decompose_subpattern_PatternContexts_full in H6. *)
    * eapply invert_a_App_Role in H4; autofwd.
      cbn in IHMatchSubst.
      eapply dsp_sub_rel in H17.
      move: H3 H0 IHMatchSubst => /= H3 H0.
      move/(_ ltac:(ok)).
      move /(_ _ _ _ _ _ _ H3 H4 _ H17 _).
      ecbn.
      invs H5.
      invs H8.
      move/(_ _ eq_refl eq_refl ltac:(eassumption)).
      introfwd.
      eexists.
      eapply chain_open_telescope_partial_subst_Rel in H10; try eassumption.
      ok.
      (* Substituted typing *)
      {
        eapply Typing_tm_subst.
        move: H11.
        ecbn.
        intros; eassumption.
        by inversion H8.
      }
      (* x ∉ dom Γ *)
      {
        autoreg.
        match goal with | H : Ctx _ |- _ => solve [by invs H] end.
      }
      (* x ∉ fv_tm_args args1 *)
      {
        have h : Pattern a1 by eapply MatchSubst_Pattern_1; eauto. (* FIXME: eauto doesn't use MatchSubst_Pattern_1 *)
        eapply pat_args_default_fv in h.
        by ok.
      }

      by ok.

    * (* invs H4. *)
      eapply invert_a_App_Role in H4; autofwd.
      move: H3 H0 IHMatchSubst => /= H3 H0.
      move/(_ ltac:(ok)).
      eapply dsp_invert_rel in H9; autofwd. eapply dsp_sub_rel in H12.
      subst.
      move /(_ _ _ _ _ _ _ H3 H4 eq_refl H12 _ ltac:(inversion H8; eassumption)).
      ecbn.
      simpl_env.
      move/(_ eq_refl).
      introfwd.
      simpl_env in H9.
      rewrite app_assoc in H9.
      eapply (@chain_open_telescope_partial_subst_general_rel _ _ _ _ _ _ _ nil) in H9; first last.
      (* Typing of A *)
      { ok. }

      (* x ∉ fv_tm_args args0 *)
      {
        fold (@app pattern_arg). (* FIXME *)
        (*__ CURRENTLY IMPORTING THE PROOF __*)
        admit.
      }


      (* x0 ∉ dom Γ *)
      {
        autoreg.
        (* FIXME: fragile *)
        eapply Ctx_uniq in _Typing_Ctx_.
        inversion _Typing_Ctx_.
        move: H17.
        simpl_env.
        ok.
      }

      (* Big existential *)
      {
        simpl_env in H11.
        ok.
        fold (@app pattern_arg) in H9. (* FIXME *)
        ecbn in H9.
        move eq: (coargs ++ pattern_arg_Rel (a_Var_f x) R :: pat_args_default a1) => old.
        (*__ CURRENTLY IMPORTING THE PROOF __*)
        admit.
      }

      (* PatCtxTrim ... *)
      {
        match goal with [ H : args_proper_type _ _ _ |- _ ] => invs H end.
        simpl_env.
        ok.
      }


  - (* Irrel *)
    admit.


  - (* Coe *)
    admit.
Admitted.






Lemma typing_args_proper_type : `{
  (* TODO: some hypotheses might not be necessary *)
  chain_open_telescope_deq Γ A PiB args_a →
  PatternContexts Ωp1 Γp1 F PiB p1 B1 →
  length args_a = length Γp1 →
  forall a,
  Γ ⊨ a : A →
  pat_args_default a = args_a → 
  pat_head a = Some F →
  Pattern a →
  (* subpattern p1' p1 → *)
  tm_pattern_agree a p1 →
  args_proper_type Γ args_a Γp1 /\
  DefEq Γ (dom Γ) (subst_args_in_term Γp1 args_a B1) A a_Star Rep
}.
Proof.
  intros until 3.
  move=> a.
  revert all except a.
  induction a; intros;
    try match goal with [H : Pattern _ |- _] => solve [inversion H] end.

  - (* Rel/Irrel *)
    intros.
    destruct nu;
    cbn in H3;
    subst.
    + destruct Γp1; simpl in H1; inversion H1.
      move: (invert_a_App_Role H2) => [A2 [B2 [TA1 [TA2 TA3]]]]; subst.
      invs H0;
        match goal with
          H : tm_pattern_agree _ _ |- _ => inversion H
        end.
      all: exactly 1 goal.

      eapply invert_cotd_ArgRel in H; first last;
        try eassumption.

      all: exactly 1 goal.
      autofwd.

      eapply IHa1 in H; try done.
      2: { clear H0; eassumption. }
      all: try eassumption.
      2: { match goal with H : Pattern _ |- _ => solve [inversion H; done] end. }
      all: exactly 1 goal. (* Done applying induction *)

      clear IHa1 IHa2.
      autofwd.
      ecbn in H1.
      move: E_PiFst; move/(_ _ _ _ _ _ _ _ _ H1) => deq1.
      move: E_PiSnd; move/(_ _ _ _ _ _ _ _ _ _ _ H1) => deq2.
      split.

      { eapply E_Sym in deq1; autoreg; econstructor; try done; eapply E_Conv; eassumption. }
      { eapply invert_a_App_Role in H2; autofwd.
        eapply E_Conv in TA2; first last; [| by eapply E_Sym; eassumption |]; [by autoreg |].
        move: (E_Refl _ (dom Γ) _ _ Nom TA2) => TA2refl.
        eapply deq2 in TA2refl.
        move: (E_Trans _ _ _ _ _ _ _ TA2refl (E_Sym _ _ _ _ _ _ TA3)).
        admit. (* QUESTION *)
      }

    + (* Irrel *)
      (* Getting rid of rho = Rel, which is impossible in a pattern (has to be a role instead) *)
      destruct rho.
      all: match goal with [ H : tm_pattern_agree _ _ |- _ ] => try solve [inversion H] end.

      admit.

  - (* CApp *)
    admit.

  - (* Head *)
    cbn in *.
    match goal with H : Some _ = Some _ |- _ => invs H end.
    cbn in *.
    match goal with H : 0 = length _ |- _ => symmetry in H; eapply length_zero_iff_nil in H end; subst.
    match goal with H : chain_open_telescope_deq _ _ _ _ |- _ => dependent induction H end;
    match goal with H : PatternContexts _ _ _ _ _ _ |- _ => invs H end.
    all: cbn; split; try solve [econstructor | by eapply E_Refl].
    eapply E_Trans;
      (* This is essentially an eassumption *)
      try solve [eapply E_Sub; [eassumption | destruct R; econstructor]].
    all: exactly 1 goal.
    eapply IHchain_open_telescope_deq; try done.
    autoreg; destruct R; eapply E_Conv; ok.
Admitted.


Lemma chain_open_telescope_deq_partial_internal_functionality : `{
  Γ ⊨ A1 : a_Star →
  chain_open_telescope_deq Γ A1 PiB args →
  forall A2,
  chain_open_telescope_partial Γ A2 PiB args →
    DefEq Γ (dom Γ) A1 A2 a_Star Rep
}.
Proof.
  intros until 1.
  move=> h; dependent induction h.
  - move=> a2 h; dependent induction h. ok.
  - move=> a2 cpo2; dependent induction cpo2.
    + eapply E_Trans.
      eapply E_Sym.
      eapply E_Sub in H0. eassumption.
      by destruct R.
      eapply IHh.
      by autoreg. ok.
    + eapply E_Trans.
      eapply E_Sym.
      eapply E_Sub.
      exact H0. by destruct R.
      eapply IHh. by autoreg.
      eapply cotp_rel; eassumption.
    + eapply E_Trans.
      eapply E_Sym.
      eapply E_Sub.
      exact H0. by destruct R.
      eapply IHh. by autoreg.
      eapply cotp_irr; eassumption.
    + eapply E_Trans.
      eapply E_Sym.
      eapply E_Sub.
      exact H0. by destruct R.
      eapply IHh. by autoreg.
      eapply cotp_capp; eassumption.
  - move=> a2 cpo2; dependent induction cpo2.
    + move: (chain_open_telescope_deq_Reg h) IHh => reg.
      move/(_ ltac:(by eassumption) _ cpo2) => eq.
      move: (where_is_this eq) => eqrho.
      rewrite eqrho in eq.
      eapply E_PiSnd in eq; try eassumption.
      by eapply E_Refl in H0; eassumption.
  - move=> a2 cpo2; dependent induction cpo2.
    + admit. (* FIXME: broken by the change in chain_open_telescope_deq about
                irrel arguments. Need to figure it out *)
      (*
      move: (chain_open_telescope_deq_Reg h) IHh => reg.
      move/(_ ltac:(by eassumption) _ cpo2) => eq.
      move: (where_is_this eq) => eqrho.
      rewrite eqrho in eq.
      eapply E_PiSnd in eq; try eassumption.
      by eapply E_Refl in H0; eassumption. *)
  - move=> a2 cpo2; dependent induction cpo2.
    + move: (chain_open_telescope_deq_Reg h) IHh => reg.
      move/(_ ltac:(by eassumption) _ cpo2) => eq.
      move: (eq) => eq2.
      eapply E_CPiSnd in eq; try eassumption.
      * admit.
        (* TODO (HELP): pretty sure there's a generalization lemma somewhere..?
           Possibly in erase.v or erase_syntax.v. It should allow to conclude
           from `eq`. *)
      * destruct R; unfold param; destruct str; cbn; ok.
      * destruct R0; unfold param; destruct str; cbn; ok.
Admitted.


Theorem MatchSubst_preservation : `{
  MatchSubst a p1 b1 b' →
  Rename p b p1 b1 ((fv_tm_tm_tm a) ∪ (fv_tm_tm_tm p)) D →
  binds F (Ax p b PiB R1 Rs) toplevel →
(*  Γ' ⊨ b : A'' → *)
  Γ ⊨ a : A →
  Γ ⊨ b' : A}.
Proof.
  intros until 0.
  move=> ms rn bds tpg_a.

  (* Deriving basic facts *)
  move: (Rename_Pattern rn) => [pat_p pat_p1].
  move: (toplevel_inversion bds) => [Ωp] [Γp] [B] [patctx_p] [tpg_b] [roleing rnge].
  move: (MatchSubst_match ms) => a_agree_p1.
  move: (Rename_spec rn) => [fv_p1 fv_b1].
  have fv_p1a : fv_tm_tm_tm p1 ∩ fv_tm_tm_tm a [=] empty by fsetdec.
  move: (Rename_PatCtx_Typing_exist rn patctx_p tpg_b) => [Ωp1] [Γp1] [B1] [patctx_p1] tpg_b1.
  move: (decompose_subpattern_refl patctx_p1) => [args_p1] dsp_p1.
  move: (Typing_regularity tpg_a) => tpg_A.

  (* First key lemma: getting a cpo on the type of a *) (* FIXME: better name *)
  move: invert_cons_ln.
  move/(_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bds patctx_p rn tpg_a _ a_agree_p1 (SubPat_Refl _ pat_p1)) => cot_a.

  (* Interlude: a's arguments have the proper types *)
  have tp_args: args_proper_type Γ (pat_args_default a) Γp1. admit. (* TODO: from typing_args_proper_type *)

 (* Second key lemma: getting a typing for b' and a cot on its type *) (* FIXME: name *)
  move: (@TODO_name).
  move/(_ _ _ _ _ _ _ _ _ _ _ _ patctx_p1 fv_p1a ms _ _ _ _ _ _ tpg_b1 tpg_a eq_refl dsp_p1) => /=.
  move/(_ eq_refl).
  move/(_ tp_args).
  move=> [B'] [cot_b'] tpg_b'.

  (* Third key lemma: "Functionality" of chain_open_telescope_deq wrt chain_open_telescope_partial *)
  move: (@chain_open_telescope_deq_partial_internal_functionality).
  move/(_ _ _ _ _ tpg_A cot_a _ cot_b') => eq_AB'.

  (* Converting b' to A *)
  move: (E_Conv).
  move/(_ _ _ _ _ tpg_b' (E_Sym _ _ _ _ _ _ eq_AB') tpg_A).

  done.
Admitted.


Lemma Beta_preservation : `(Beta a b R →  forall G A, Typing G a A -> Typing G b A).
Proof.
(*
  induction 1; intros G A0 TH.
  - have CT: Ctx G by eauto.
    have RA: Typing G A0 a_Star by eauto using Typing_regularity.
    destruct rho.
    + destruct (invert_a_App_Rel TH) as (A & B & TB & DE & h).
      destruct (invert_a_UAbs TB) as (A1 & B1 & DE2 & [L TB1] & TA1 ).
      eapply E_Conv with (A := (open_tm_wrt_tm B1 b)); eauto 2.
      pick fresh x.
      move: (TB1 x ltac:(auto)) =>  [T1 [T2 RC]].
      rewrite (tm_subst_tm_tm_intro x v); eauto 2.
      rewrite (tm_subst_tm_tm_intro x B1); eauto.

      eapply Typing_tm_subst with (A:=A1); eauto 5.
      eapply E_Sym.
      eapply E_Trans with (a1:= open_tm_wrt_tm B b); eauto 2.
      eapply E_PiSnd; eauto 1.
      eauto.

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
      eapply E_Conv with (A:=A); eauto using E_PiFst, param_sub1.
      eapply E_Sym.
      eapply E_Trans with (a1 := open_tm_wrt_tm B b0). auto.
      eapply E_PiSnd; eauto using E_Refl, param_covariant.
   - have CT: Ctx G by eauto.
     have RA: Typing G A0 a_Star by eauto using Typing_regularity.
     destruct (invert_a_CApp TH) as (eq & a1 & b1 & A1 & R1 & B1 & h0 & h1 & h2 ).
     destruct (invert_a_UCAbs h0) as (a2 & b2 & A2 & R3 & B2 & h4 & h5 & [L h6] ).
     pick fresh c.
     move: (h6 c ltac:(auto)) => [T1 T2].
     have? : DefEq G (dom G) a2 b2 A2 R3. 
     apply E_CPiFst in h5. apply E_Cast in h5. auto.
     eapply E_Sub; eauto using param_sub1.
     eapply E_Conv with (A:= (open_tm_wrt_co B2 g_Triv)); eauto 2.
     rewrite (co_subst_co_tm_intro c a'); eauto.
     rewrite (co_subst_co_tm_intro c B2); eauto.
     eapply Typing_co_subst; eauto.
     eapply E_Sym.
     eapply E_Trans with (a1 := open_tm_wrt_co B1 g_Triv). auto.
     eapply E_CPiSnd; eauto 2.
     apply E_CPiFst in h5. apply E_Cast in h5; auto 1.
     all: rewrite param_rep_r; eauto 2.
   -
     autofwd.
     autoinv.
     move: H.
     move/toplevel_inversion. introfwd.
     eapply MatchSubst_preservation.
     eauto 1.
     eauto 1.
     eapply H.
     eauto 1.
     eauto 1.
   
(*      destruct (invert_a_Fam TH) as [(b & h1 & h2 & h3) | (b & B & R2 & h1 & h2 & h3)].
     assert (Cs b = Ax a A R). eapply binds_unique; eauto using uniq_toplevel.
     inversion H1.
     assert (Ax a A R = Ax b B R2). eapply binds_unique; eauto using uniq_toplevel.
     inversion H1. subst. clear H1.
     eapply E_Conv with (A := B).
     eapply toplevel_closed in h2.
     eapply Typing_weakening with (F:=nil)(G:=nil)(E:=G) in h2; simpl_env in *; auto.
     eapply E_SubRole; eauto 1.
     eauto 2.
     eapply E_Sym. eauto.
     eapply Typing_regularity. 
     eauto. *)

   - dependent induction TH.
     + eapply E_Conv.
       eapply IHTH1; try eauto.
         eauto.
         ok.
     + autofresh.
       erewrite <- open_tm_wrt_co_lc_tm; last first.
       * eapply BranchTyping_lc_last in H2. eauto.
       * eapply E_CApp.

   - dependent induction TH; eauto.
     Unshelve. exact (dom G). exact (dom G).
*)
Admitted.


Lemma E_Beta2 :  ∀ (G : context) (D : available_props) (a1 a2 B : tm) R,
       Typing G a1 B → Beta a1 a2 R → DefEq G D a1 a2 B R.
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
    ok.
    ok.
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
  - (* TODO: missing lemma
    apply toplevel_closed_axiom in H.
    move: (Typing_context_fv H) => ?. split_hyp.
    simpl in *.
    fsetdec. *)
    admit.
  - admit.
  - admit.
  - eauto.
  - admit.
  - eauto.
Admitted.

Lemma reduction_in_Par : forall a a' R, reduction_in_one a a' R ->
                                   forall W, roleing W a R -> Par W a a' R.
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
    + inversion H; subst.
     (* eapply Par_Axiom; eauto. eapply rctx_uniq in H0. auto. *)
     all: admit.
    + inversion H0; subst. eapply Par_PatternTrue; eauto.
    + inversion H0; subst. (* eapply Par_PatternFalse; eauto *) admit.
Admitted.




Lemma reduction_in_one_fv_preservation: forall x a b R W , reduction_in_one a b R -> roleing W a R ->
                                        x `notin` fv_tm_tm_tm a ->
                                        x `notin` fv_tm_tm_tm b.
Proof.
  intros.
  eapply Par_fv_preservation; eauto.
  eapply reduction_in_Par; eauto.
Qed.

Lemma reduction_rhocheck : forall a a' rho x R W, 
    reduction_in_one a a' R -> roleing W a R -> RhoCheck rho x a -> RhoCheck rho x a'.
Proof.
  intros.
  inversion H1; subst.
  -  eauto using reduction_in_one_lc.
  -  eauto using reduction_in_one_fv_preservation.
Qed.

Lemma reduction_preservation : forall a a' R, reduction_in_one a a' R -> forall G A, 
      Typing G a A -> Typing G a' A.
Proof.
  (* TODO: clean and make more robust *)
  move=> a a' R r.
  induction r.
  all: move=> G A_ tpga.
  - move: (Typing_regularity tpga) => h0.
    autoinv. (*
    eapply E_Conv with (A := (a_Pi Irrel x R x0)); auto.
    pick fresh y and apply E_Abs; auto.
    apply_first_hyp; auto.
    apply H2. auto. eauto.
    eapply reduction_rhocheck; eauto.
    eapply Typing_roleing; eauto.
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
    inversion tpga as [A [s [B [P1 [P2 [P3 [P4 P5]]]]]]].
    eapply E_Pat. eauto. eauto. eapply E_Conv. eauto. eauto.
    eapply DefEqIso_regularity. eapply E_Sym. eauto.
    eapply E_Conv. eauto. eauto.
    eapply DefEqIso_regularity. eapply E_Sym. eauto.
  - eapply Beta_preservation; eauto. *)
Admitted.

