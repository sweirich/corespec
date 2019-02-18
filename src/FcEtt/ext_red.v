Require Import FcEtt.imports.
Require Import FcEtt.tactics.
Require Import FcEtt.notations.

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
Require Import FcEtt.ett_path.
Require Import FcEtt.ett_match.
Require Import FcEtt.pattern.

Require Export FcEtt.ext_red_one.


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

(* FIXME: temporary *)
Generalizable All Variables.

Definition degrade : pattern_arg -> pattern_arg :=
  fun p => match p with 
  | p_Tm (Role R) a => p_Tm (Rho Rel) a
  | _ => p
  end.


(* FIXME: move *)
(* Specialize term H, using only hyps present in the context *)
Ltac spec_hyp_ctx_only H name :=
  tryif match goal with H' : _ |- _ => unify name H' end then fail 0 name "is already taken" else
  lazymatch type of H with
    | forall x : ?T, _ =>
      match goal with H' : _ |- _ => spec_hyp_ctx_only (H H') name end
    | _ => move: H; move => name
  end.


Lemma to_move : `{
  Γ ⊨ open_tm_wrt_co a g₁ : A →
  open_tm_wrt_co a g₁ = open_tm_wrt_co a g₂}.
Proof.
  intros until 0.
  move=> h; dependent induction h.
  all: try with @eq do fun h => destruct a; try solve [inv h]; cbn in h.
  all: cbn; try reflexivity.

  (* Solving one idiosyncratic goal *)
  all: try (match goal with |- open_tm_wrt_co _ _ = open_tm_wrt_co _ _ => idtac end; by move:(IHh1 _ _ eq_refl) => ->).

  all: try injection x; intros.
  all: unfold open_tm_wrt_co in *.
  all: try (spec_hyp_ctx_only IHh1 ih1; rewrite <- ih1 in * ).
  all: try (spec_hyp_ctx_only IHh2 ih2; rewrite <- ih2 in * ).
  all: try reflexivity.

Admitted.
Definition open_co := @to_move.


Notation PatCtxTrim Γ p :=
  (exists Ω F PiB B, PatternContexts Ω Γ F PiB p B).

(* Readability notations *)
(*
Notation "'ArgRel' a" := (p_Rel a _)   (at level 50). (* FIXME: level? *)
Notation "'ArgIrr' a" := (p_Irrel a _) (at level 50). (* FIXME: level? *)
Notation "'ArgCoe' a" := (p_Co a _)    (at level 50). (* FIXME: level? *)
*)

(******** Internal relations used only for proving ********)

(*  chain_open_telescope_deq G A PiB args 
    (Notated #copd: G |= A == PiB ^ args)
    represents that G |= A = "PiB opened with args" : TYPE / R *)

(* Note: technically, PiB is not just a telescope - it also stores the
   return type. We nevertheless use "telescope" in the naming
 *)
(* TODO: This relation needs to include a Role *)
Inductive chain_open_telescope_deq : context → tm → tm → pattern_args → Prop :=
  | cotd_base : 
     `{Typing Γ A a_Star →
       chain_open_telescope_deq Γ A A []}

  | cotd_eq   : 
      `{chain_open_telescope_deq Γ A B args →
        DefEq Γ (dom Γ) A C a_Star R →
        chain_open_telescope_deq Γ C B args}

  | cotd_rel  : 
      `{chain_open_telescope_deq Γ (a_Pi Rel A' A) B args →
        Typing Γ a A' →
        chain_open_telescope_deq Γ (open_tm_wrt_tm A a) B (p_Tm (Role R) a :: args)}

  | cotd_irr  : 
      `{chain_open_telescope_deq Γ (a_Pi Irrel A' A) B args →
        Typing Γ a A' →
        chain_open_telescope_deq Γ (open_tm_wrt_tm A a) B (p_Tm (Rho Irrel) a_Bullet :: args)}

  | cotd_capp : 
      `{chain_open_telescope_deq Γ (a_CPi (Eq C C' K R) A) B args →
        DefEq Γ (dom Γ) C C' K R →
        chain_open_telescope_deq Γ (open_tm_wrt_co A g) B (p_Co g :: args)}
.

Notation "#copd: G |= A == B ^ args" := (chain_open_telescope_deq G A B args) (at level 50). (* TODO: figure out the level(s) *)

Hint Constructors chain_open_telescope_deq.

(* Same than previous relation, except we don't allow the use of internal equality.
   Namely, represents A = "PiB opened with args". The base requirements are also
   weakened (no typing check).
   See above for additional details *)
Inductive chain_open_telescope_partial : context → tm → tm → pattern_args → Prop :=
  | cotp_base : 
      `{chain_open_telescope_partial Γ A A []}

  | cotp_rel  : 
      `{chain_open_telescope_partial Γ (a_Pi Rel A' A) B args →
        Typing Γ a A' →
        chain_open_telescope_partial Γ (open_tm_wrt_tm A a) B (p_Tm (Role R) a :: args)}

  | cotp_irr  : 
      `{chain_open_telescope_partial Γ (a_Pi Irrel A' A) B args →
        Typing Γ a A' →
        chain_open_telescope_partial Γ (open_tm_wrt_tm A a) B (p_Tm (Rho Irrel) a :: args)}

  | cotp_capp : 
      `{chain_open_telescope_partial Γ (a_CPi (Eq C C' K R) A) B args →
        chain_open_telescope_partial Γ (open_tm_wrt_co A g) B (p_Co g :: args)}
.

Notation "#cotp: G |= A = B ^ args" := (chain_open_telescope_partial G A B args) (at level 50). (* TODO: figure out the level(s) *)

Hint Constructors chain_open_telescope_partial.

Inductive decompose_subpattern :
  tm → tm → pattern_args → pattern_args → context → context → Prop :=
  | dsp_base : `{decompose_subpattern (a_Fam F) (a_Fam F) nil nil nil nil}

  | dsp_full_rel : `{decompose_subpattern p p args nil Γ nil →
                     PatCtxTrim (x ~ Tm A' ++ Γ') (a_App p (Role R) (a_Var_f x)) →
                     decompose_subpattern (a_App p (Role R) (a_Var_f x)) (a_App p (Role R) (a_Var_f x))
                                          (p_Tm (Role R) (a_Var_f x) :: args) nil
                                          (x ~ Tm A' ++ Γ) nil}

  | dsp_sub_rel  : `{decompose_subpattern p' p args coargs Γ coΓ →
                     PatCtxTrim (x ~ Tm A' ++ coΓ ++ Γ) (a_App p (Role R) (a_Var_f x)) →
                     decompose_subpattern p' (a_App p (Role R) (a_Var_f x))
                                             args (p_Tm (Role R) (a_Var_f x) :: coargs)
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
    args_proper_type Γ (p_Tm (Role R) a :: args) (x ~ Tm A ++ Γ')}
  (* TODO: irr/coe *)
.

Hint Constructors args_proper_type.



(******** Lemmas about these inductives ********)

Lemma chain_open_telescope_deq_Reg : `{
  chain_open_telescope_deq Γ A B args →
  Typing Γ A a_Star
}.
Proof.
(*
  induction 1; autoreg; ok;
    let ih := fresh in
    (* FIXME: switch to solve *)
    first [
      get (Typing _ (a_Pi _ _ _)) as ih;
      eapply invert_a_Pi in ih;
      autofwd; autofresh;
      move: Typing_tm_subst;
      move/(_ _ _ _ _ _ ltac:(eassumption) _ ltac:(eassumption));
      rewrite -tm_subst_tm_tm_intro; cbn; last by done; by fsetdec
    |
      (* Coe case *)
      get (Typing _ (a_CPi _ _) _) as ih;
      eapply invert_a_CPi in ih;
      autofwd; autofresh;
      move: Typing_co_subst;
      move/(_ _ _ _ _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption));
      rewrite -co_subst_co_tm_intro; cbn; try done; first by fsetdec (* FIXME: -> last by done *)
      (* TODO *)
    ]. *)
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
  chain_open_telescope_partial Γ B PiB (coargs ++ one (p_Tm (Role R) (a_Var_f x)) ++ args) →
  chain_open_telescope_partial Γ (tm_subst_tm_tm a x B) PiB (coargs ++ (p_Rel a R :: args))
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
  chain_open_telescope_partial Γ B PiB (coargs ++ one (p_Tm (Role R) (a_Var_f x)) ++ args) →
  chain_open_telescope_partial Γ (tm_subst_tm_tm a x B) PiB (coargs ++ (p_Rel a R :: args))
}.
Proof.
  (* TODO: by specialization of previous lemma (after it gets generalized) *)
Admitted.

Lemma chain_open_telescope_partial_subst_Rel : `{
  x `notin` dom Γ →
  x `notin` fv_tm_args args →
  Γ ⊨ a : A →
  chain_open_telescope_partial Γ B PiB ((p_Tm (Role R) (a_Var_f x) :: args)) →
  chain_open_telescope_partial Γ (tm_subst_tm_tm a x B) PiB ((p_Tm (Role R) a :: args))
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
  chain_open_telescope_deq Γ A PiB (p_Tm (Role R) a2 :: args) -> 
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
  args = p_Rel (a_Var_f x) R :: args' /\
  Γ = x ~ Tm A ++ Γ' /\
  decompose_subpattern a p args' (coargs ++ [p_Rel (a_Var_f x) R]) Γ' (coΓ ++ x ~ Tm A)
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
      with decompose_subpattern do ltac:(fun h => eapply dsp_sub_rel in h).
      move: H3 H0 IHMatchSubst => /= H3 H0.
      move/(_ ltac:(ok)).
      move /(_ _ _ _ _ _ _ H3 H4 _ H17 _).
      ecbn.
      invs H5.
      with args_proper_type do invs.
      move/(_ _ eq_refl eq_refl ltac:(eassumption)).
      introfwd.
      eexists.
      with chain_open_telescope_partial do ltac:(fun h => eapply chain_open_telescope_partial_subst_Rel in h; try eassumption).
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
        with Ctx do ltac:(fun h => solve [by invs h]).
      }
      (* x ∉ fv_tm_args args1 *)
      {
        have h : Pattern a1 by eapply MatchSubst_Pattern_1; eauto. (* FIXME: eauto doesn't use MatchSubst_Pattern_1 *)
        eapply pat_args_default_fv in h.
        by ok.
      }

      by ok.

    * (* invs H4. *)
      with (Typing _ (a_App _ _ _)) do ltac:(fun h => eapply invert_a_App_Role in h; autofwd).
      get (Typing ((_, _) :: _)) as h3.
      get (_ [=] empty) as h0.
      move: h3 h0 IHMatchSubst => /= h3 h0.
      move/(_ ltac:(ok)).
      with decompose_subpattern do ltac:(fun h => eapply dsp_invert_rel in h; autofwd; rename h into h1).
      with decompose_subpattern do ltac:(fun h => eapply dsp_sub_rel in h; rename h into h2).
      subst.
      get (Typing _ _ (a_Pi _ _ _)) as h4.
      get args_proper_type as h8.
      move /(_ _ _ _ _ _ _ h3 h4 eq_refl h2 _ ltac:(inversion h8; eassumption)).
      ecbn.
      simpl_env.
      move/(_ eq_refl).
      introfwd.
      get chain_open_telescope_partial as h5.
      eapply (@chain_open_telescope_partial_subst_general_rel _ _ _ _ _ _ _ nil) in h5; first last.
      (* Typing of A *)
      { ok. }

      (* x ∉ fv_tm_args args0 *)
      {
        fold (@app pattern_arg). (* FIXME *)
        admit.
      }


      (* x0 ∉ dom Γ *)
      {
        autoreg.
        get (Ctx (_ ++ _)) as h6.
        eapply Ctx_uniq in h6.
        inversion h6.
        match goal with
          H : ?x ∉ _ |- ?x ∉ _ => move: H; simpl_env; by ok
        end.
      }

      (* Big existential *)
      {
        simpl_env in H4.
        ok.
        fold (@app pattern_arg) in h5. (* FIXME *)
        ecbn in h5.
        move eq: (coargs ++ p_Tm (Role R) (a_Var_f x) :: pat_args_default a1) => old.
        all: admit.
      }

      (* PatCtxTrim ... *)
      {
        with args_proper_type do invs.
        simpl_env.
        ok.
      }


  - (* Irrel *)
    admit.


  - (* Co *)
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
    try with Pattern do fun h => solve [inv h].

  - (* Rel/Irrel *)
    intros.
    destruct nu;
    cbn in H3;
    subst.
    + destruct Γp1; simpl in H1; inversion H1.
      move: (invert_a_App_Role H2) => [A2 [B2 [TA1 [TA2 TA3]]]]; subst.
      invs H0; with tm_pattern_agree do ltac:(fun h => inversion h).
      all: exactly 1 goal.

      eapply invert_cotd_ArgRel in H; first last;
        try eassumption.

      all: exactly 1 goal.
      autofwd.

      eapply IHa1 in H; try done.
      2: { clear H0; eassumption. }
      all: try eassumption.
      2: { with Pattern do ltac:(fun h => solve [inversion h; done]). }
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
      all: with tm_pattern_agree do ltac:(fun h => try solve [inversion h]).

      admit.

  - (* CApp *)
    admit.

  - (* Head *)
    cbn in *.
    match goal with H : Some _ = Some _ |- _ => invs H end.
    cbn in *.
    match goal with H : 0 = length _ |- _ => symmetry in H; eapply length_zero_iff_nil in H end; subst.
    with chain_open_telescope_deq do ltac:(fun h => dependent induction h) end;
    with PatternContexts do invs.
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
  - move=> a2 cpo2; dependent induction cpo2; exactly 1 goal.
    move: IHh.
    move/(_ ltac:(eauto using chain_open_telescope_deq_Reg) _ cpo2).
    move/(E_PiSnd _).
    apply.
    eauto.
  - move=> a2 cpo2; dependent induction cpo2; exactly 1 goal.
    move: IHh.
    move/(_ ltac:(eauto using chain_open_telescope_deq_Reg) _ cpo2).
    move/(E_PiSnd _).
    move/(_ a a (E_Refl _ _ _ _ _ ltac:(ea))) => p.
    (* FIXME: irr arguments are broken atm *)
    admit.
  - move=> a2 cpo2; dependent induction cpo2; exactly 1 goal.
    move: (chain_open_telescope_deq_Reg h) IHh => reg.
    move/(_ ltac:(by eassumption) _ cpo2) => eq.
    move: (eq) => eq2.
    eapply E_CPiSnd in eq; try eassumption.
    * autoreg.
      (* FIXME fragile *)
      erewrite (to_move _a1_) in eq.
      erewrite (to_move _b1_) in eq.
      by eassumption.
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

 (* Second key lemma: getting a typing for b' and a cot on its type *) 
  (* FIXME: name *)
  move: (@TODO_name).
  move/(_ _ _ _ _ _ _ _ _ _ _ _ patctx_p1 fv_p1a ms _ _ _ _ _ _ tpg_b1 tpg_a eq_refl dsp_p1) => /=.
  move/(_ eq_refl).
  move/(_ tp_args).
  move=> [B'] [cot_b'] tpg_b'.

  (* Third key lemma: "Functionality" of chain_open_telescope_deq wrt 
     chain_open_telescope_partial *)
  move: (@chain_open_telescope_deq_partial_internal_functionality).
  move/(_ _ _ _ _ tpg_A cot_a _ cot_b') => eq_AB'.

  (* Converting b' to A *)
  move: (E_Conv).
  move/(_ _ _ _ _ tpg_b' (E_Sym _ _ _ _ _ _ eq_AB') tpg_A).

  done.
Admitted.


(* --------------------------------------------------------- *)


Definition domFresh {a} (sub:list (atom * a)) s :=
  Forall (fun '(x,_) => x `notin` s) sub.

Lemma domFresh_cons : forall A x (st:A) Gp s,
 domFresh (x ~ st ++ Gp) s -> 
 x `notin` s /\ (domFresh Gp s).
Proof. 
  intros.
  unfold domFresh in *.  inversion H. auto.
Qed. 

Lemma domFresh_union : forall (G:list (atom*sort)) s1 s2,
 domFresh G (s1 `union` s2) -> 
 domFresh G s1 /\ (domFresh G s2).
Proof.
  induction G; intros; unfold domFresh in *. eauto.
  inversion H. edestruct IHG; eauto.
  destruct a.
  repeat split; eauto.
Qed. 

(* --------------------------------------------------------- *)

(* Chain (multi-) substitutions *)

(* 
   Give a context (G) and a list of pattern_args (args), we can create 
   a multi-substitution as 

       sub := zip (fst G) args 

*)

(* TODO: generate this with ott?? *)
Definition pattern_arg_subst_tm : pattern_arg -> atom -> tm -> tm :=
 fun arg x b =>
  match arg with 
  | p_Tm nu a => tm_subst_tm_tm a x b
  | p_Co _    => co_subst_co_tm g_Triv x b
  end.


(* This operation applies that substitution to an arbitrary tm *)
Definition chain_pattern_substitution : tm -> list (atom * pattern_arg) -> tm :=
  fold_right (fun '(x,y) b => pattern_arg_subst_tm y x b).

Definition cps_constraint phi sub :=
  match phi with 
  | Eq a b A R => Eq (chain_pattern_substitution a sub)
                    (chain_pattern_substitution b sub)
                    (chain_pattern_substitution A sub)
                    R
  end.
Definition cps_sort (s : sort) sub :=
  match s with 
  | Tm A => Tm (chain_pattern_substitution A sub)
  | Co phi => Co (cps_constraint phi sub)
  end.

Definition cps_context (G : context) su : context :=
  EnvImpl.map (fun so => cps_sort so su) G.

(* Predicates about these substitutions *)

Definition lc_sub (sub:list(atom*pattern_arg)) :=
  Forall (fun '(x,p) => lc_pattern_arg p) sub.


Definition rngFresh x (sub:list(atom*pattern_arg)) :=
  Forall (fun '(y,t) => x `notin` singleton y `union` (fv_tm_tm_pattern_arg t)) sub.

(* cps properties --- homemorphic over term forms *)

Lemma cps_CPi : forall phi C sub, 
    chain_pattern_substitution (a_CPi phi C) sub = 
        (a_CPi (cps_constraint phi sub) 
               (chain_pattern_substitution C sub)).
Proof.
  intros. induction sub; destruct phi; simpl; auto.
  destruct a; simpl; rewrite IHsub.
  destruct p; simpl; auto.
Qed.

Lemma cps_Pi : forall A B sub,
   chain_pattern_substitution (a_Pi Rel A B) sub = 
               a_Pi Rel (chain_pattern_substitution A sub)
                        (chain_pattern_substitution B sub).
Proof. 
  intros. induction sub; simpl; auto.
  destruct a; simpl. rewrite IHsub.
  destruct p; simpl; auto.
Qed.

Lemma cps_app : forall l nu a1 a2,
           chain_pattern_substitution (a_App a1 nu a2) l =
           a_App (chain_pattern_substitution a1 l) nu 
                 (chain_pattern_substitution a2 l).
Proof. intros. induction l. simpl; auto. 
       destruct a; simpl. rewrite IHl.
       destruct p; simpl; auto.
Qed.

Lemma cps_capp : forall l a, chain_substitution (a_CApp a g_Triv) l =
                       a_CApp (chain_substitution a l) g_Triv.
Proof. intros. induction l. simpl; auto. destruct a0; simpl. rewrite IHl; auto.
Qed.



Lemma cps_cons_Tm : forall nu a x s sub1, 
  tm_subst_tm_tm a x (chain_pattern_substitution s sub1) =
  chain_pattern_substitution s ((x, p_Tm nu a) :: sub1).
Proof.
  intros. simpl. auto.
Qed.

Lemma cps_nil : forall s,
  chain_pattern_substitution s ∅ = s.
Proof. 
  intros. auto.
Qed.


Lemma cps_sort_cons : forall a x s nu sub1, 
  tm_subst_tm_sort a x (cps_sort s sub1) =
  cps_sort s ((x, p_Tm nu a) :: sub1).
Proof.
  intros. destruct s. simpl. auto. simpl. 
  destruct phi. simpl. auto.
Qed.

Lemma cps_sort_nil : forall s,
  cps_sort s ∅ = s.
Proof. 
  destruct s. simpl. auto.
  destruct phi. simpl. auto.
Qed.



Lemma tm_subst_tm_tm_cps: forall b a x sub, 
    domFresh sub (fv_tm_tm_tm a) ->
    domFresh sub (fv_co_co_tm a) ->
    rngFresh x sub ->
    tm_subst_tm_tm a x (chain_pattern_substitution b sub)
    = chain_pattern_substitution (tm_subst_tm_tm a x b) sub.
Proof.
  induction sub.  simpl. auto.
  move=> DF1 DF2 DF3.
  inversion DF1. inversion DF2. inversion DF3.
  destruct a0. simpl.
  destruct p; simpl.
  rename a0 into y.
  rewrite <- IHsub; auto.
  rewrite (tm_subst_tm_tm_tm_subst_tm_tm _ a). auto.  auto.
  rewrite (tm_subst_tm_tm_fresh_eq a1). auto.
  auto.
  rewrite <- IHsub; auto.
  rewrite (tm_subst_tm_tm_co_subst_co_tm _ a). auto.
  simpl.
  auto. 
Qed.


(* TODO: more freshness constraints for this lemma *)
Lemma cps_subst_var : forall sub0 x nu a2,  
    ¬ In x (map fst sub0) ->
     chain_pattern_substitution (a_Var_f x) ((x, p_Tm nu a2) :: sub0) = a2.
Proof.
  intros.
  simpl.
  rewrite tm_subst_tm_tm_cps.
  admit.
  admit.
  admit.
  rewrite tm_subst_tm_tm_var.
  admit.
Admitted.



Lemma cps_open_tm_wrt_tm : forall C a sub,
    lc_sub sub ->
    chain_pattern_substitution (open_tm_wrt_tm C a) sub
     = open_tm_wrt_tm (chain_pattern_substitution C sub) 
                      (chain_pattern_substitution a sub).
Proof.
  induction sub. simpl. auto.
  move=> LC. inversion LC.
  simpl. destruct a0. destruct p; simpl.
  inversion H1.
  rewrite IHsub; auto.
  rewrite tm_subst_tm_tm_open_tm_wrt_tm; auto.
  inversion H1.
  rewrite IHsub; auto.
  rewrite co_subst_co_tm_open_tm_wrt_tm. auto.
  auto.
Qed.



(* --------------------------------------------------------- *)

Lemma apply_pattern_args_tail_Tm : forall rest a b nu,
   apply_pattern_args a (rest ++ [p_Tm nu b]) = 
   a_App (apply_pattern_args a rest) nu b.
Proof. 
  induction rest. simpl. auto.
  intros.
  rewrite <- app_comm_cons.
  destruct a; simpl; rewrite IHrest; auto.
Qed. 
Lemma apply_pattern_args_tail_Co : forall rest a b,
 apply_pattern_args a (rest ++ [p_Co b]) = 
   a_CApp (apply_pattern_args a rest) b.
Proof. 
  induction rest. simpl. auto.
  intros a0 b.
  rewrite <- app_comm_cons.
  destruct a; simpl; rewrite IHrest; auto.
Qed.

Fixpoint args_roles ( l : list pattern_arg) : list role :=
   match l with 
        | nil => nil
        | ( (p_Tm (Role R) _) :: xs ) => R :: args_roles xs 
        | ( (p_Tm (Rho Rel) _)  :: xs ) => Nom :: args_roles xs
        | ( (p_Tm (Rho Irrel) _)  :: xs ) => args_roles xs
        | ( (p_Co _         ) :: xs)  => args_roles xs  
        end.

Lemma args_roles_app : forall l1 l2, 
    args_roles (l1 ++ l2) = args_roles l1 ++ args_roles l2.
Proof. 
  induction l1; intros; eauto. 
  destruct a; try destruct nu; try destruct rho; simpl; rewrite IHl1; eauto.
Qed.
  
Lemma ApplyArgs_pattern_args : forall a b1 b1' F,
 ApplyArgs a b1 b1' 
 -> ValuePath a F
 -> exists args, a = apply_pattern_args (a_Fam F) args 
       /\ b1' = apply_pattern_args b1 (map degrade args).
Proof.
  induction 1.
  + move=> VP. exists nil.  
    inversion VP; subst.
    repeat split; eauto.
    repeat split; eauto.
  + move=> VP. inversion VP; subst.
    move: (IHApplyArgs ltac:(auto)) => [rest [h0 h1]].
    rewrite h0. rewrite h1.
    exists (rest ++ [p_Tm (Role R) a']).
    rewrite map_app. simpl.
    rewrite! apply_pattern_args_tail_Tm.
    repeat split; auto.
  + move=> VP. inversion VP; subst.
    move: (IHApplyArgs ltac:(auto)) => [rest [h0 h1]].
    rewrite h0. rewrite h1.
    exists (rest ++ [p_Tm (Rho rho) a']).
    rewrite map_app. simpl.
    rewrite! apply_pattern_args_tail_Tm.
    auto.
  + move=> VP. inversion VP; subst.
    move: (IHApplyArgs ltac:(auto)) => [rest [h0 h1]].
    rewrite h0. rewrite h1.
    exists (rest ++ [p_Co g_Triv]).
    rewrite map_app. simpl.
    rewrite! apply_pattern_args_tail_Co. auto.
Qed.


Definition arg_app (p : pattern_arg) : App := 
    match p with 
      | p_Tm nu _ => A_Tm nu
      | p_Co _    => A_Co
    end.

Fixpoint map_arg_app (p : list pattern_arg) : Apps :=
  match p with 
  | nil => A_nil
  | cons arg args => A_cons (arg_app arg) (map_arg_app args)
  end.


(* This is a slightly different version of chain_open_telescope_deq that 
   works a little better in the proofs below.

   open_telescope G n PiB args targs A 

   holds when 
      - the args line up with n
      - each arg matches the Pis in B and produces a final type A
 *)

Inductive open_telescope : context -> Apps -> tm -> pattern_args -> pattern_args -> tm -> Prop :=
  | open_base : forall G A,
      Typing G A a_Star ->
      open_telescope G A_nil A nil nil A
  | open_Role : forall G apps a A R B B0 args targs C,
      Typing G a A ->
      open_telescope G apps B0 args targs C ->
      DefEq G (dom G) B0 (open_tm_wrt_tm B a) a_Star Rep ->
      open_telescope G (A_cons (A_Tm (Role R)) apps) (a_Pi Rel A B) (p_Tm (Role R) a :: args) (p_Tm (Role R) a :: targs) C
  | open_Rel : forall G apps a A B B0 args targs C,
      Typing G a A ->
      open_telescope G apps B0 args targs C ->
      DefEq G (dom G) B0 (open_tm_wrt_tm B a) a_Star Rep -> 
      open_telescope G (A_cons (A_Tm (Rho Rel)) apps) (a_Pi Rel A B) (p_Tm (Rho Rel) a :: args) (p_Tm (Rho Rel) a :: args) C
  | open_Irrel : forall G apps a A B B0 args targs C,
      Typing G a A ->
      open_telescope G apps B0 args targs C ->
      DefEq G (dom G) B0 (open_tm_wrt_tm B a) a_Star Rep ->
      open_telescope G (A_cons (A_Tm (Rho Irrel)) apps) (a_Pi Irrel A B) (p_Tm (Rho Irrel) a_Bullet :: args)
                                        (p_Tm (Rho Irrel) a :: targs)  C
  | open_Co : forall G apps a b A R B B0 args targs C,
      DefEq G (dom G)  a b A R ->
      open_telescope G apps B0 args targs C ->
      DefEq G (dom G) B0 (open_tm_wrt_co B g_Triv) a_Star Rep ->
      open_telescope G (A_cons A_Co apps) (a_CPi (Eq a b A R) B) (p_Co g_Triv :: args)  (p_Co g_Triv :: targs) C
.

Hint Constructors open_telescope.

Lemma invert_Typing_pattern_args2 : forall args hd,
  forall G A, Typing G (apply_pattern_args hd args) A -> 
  exists PiB targs, open_telescope G (map_arg_app args) PiB args targs A
   /\ G ⊨ hd : PiB.
Proof.   
  induction args; intros hd G A H.
  + reg H. simpl. eauto. 
  + destruct a. 
    ++ simpl in H.
       destruct (IHargs _ G A H) as [PiB [targs h0]]. split_hyp.
       destruct nu; try destruct rho; autoinv.
       - do 2 eexists; split; last by eauto 1.
         eapply open_Role; eauto 1. 
       - do 2 eexists; split; last by eauto 1.
         eapply open_Rel; eauto 1.
       - do 2 eexists; split; last by eauto 1.
         subst.
         eapply open_Irrel; eauto 1.
    ++ simpl in H.
       destruct (IHargs _ G A H) as [PiB [targs h0]]. split_hyp.
       autoinv. eexists; eexists; split; eauto 1.
       subst.
       eapply open_Co; eauto 1.
Qed.

Lemma invert_Typing_pattern_args3 : forall args hd,
  forall G A F Rs, 
    RolePath (apply_pattern_args hd args) F Rs ->
    Typing G (apply_pattern_args hd args) A -> 
  exists PiB targs, open_telescope G (map_arg_app args) PiB args targs A
   /\ G ⊨ hd : PiB /\ RolePath hd F (args_roles args ++ Rs).
Proof.   
  induction args; intros hd G A F Rs RP H.
  + reg H. simpl. 
    exists A. exists nil.
    repeat split; auto.
  + destruct a. 
    ++ simpl in H.
       destruct (IHargs _ G A F Rs RP H) as [PiB [targs h0]]. split_hyp.
       destruct nu; try destruct rho; autoinv.
       - do 2 eexists; repeat split; eauto 1.
         eapply open_Role; eauto 1.
         inversion H2. simpl. auto.
       - do 2 eexists; repeat split; eauto 1. 
         eapply open_Rel; eauto 1.
         inversion H2. 
       - subst. inversion H2. subst. 
         do 2 eexists. repeat split.
         eapply open_Irrel; eauto 1.
         eauto 1. simpl. auto.
    ++ simpl in H.
       destruct (IHargs _ G A F Rs RP H) as [PiB [targs h0]]. split_hyp.
       autoinv. subst. 
       eexists; eexists; repeat split; eauto 1.
       eapply open_Co; eauto 1.
       inversion H2. subst. simpl. auto.
Qed.


Lemma Typing_a_Fam_unique : forall F G A B, 
      Typing G (a_Fam F) A -> Typing G (a_Fam F) B -> DefEq G (dom G) A B a_Star Rep.
Proof.
  intros.
  autoinv.
  all: match goal with 
      | [ H : binds _ _ _ , H1 : binds _ _ _ |- _ ] => 
        move: (binds_unique _ _ _ _ _ H3 H1 uniq_toplevel) => e ;
        inversion e                                                               
      end.
  + subst.
    eapply E_Trans; eauto 1.
    eapply E_Sym; eauto 1.
  + subst.
    eapply E_Trans; eauto 1.
    eapply E_Sym; eauto 1.
Qed.

(* Currently unusud, but could be useful *)

Inductive BaseType : tm -> Prop :=
  | BaseType_Star : BaseType a_Star
  | BaseType_Path : forall a F, ValuePath a F -> BaseType a.

(* ConstType A holds when 
      A is of the form Pi Tele . B  where B is a base type
*)
(*
Inductive ConstType : list App -> tm -> Prop := 
 | ConstBase : forall A, 
    BaseType A -> ConstType nil A 
 | ConstPi   : forall n rho A B,
     (forall x, ConstType n (open_tm_wrt_tm B (a_Var_f x))) ->
     ConstType (A_Tm rho :: n) (a_Pi rho A B)
 | ConstCPi   : forall n phi B , 
     (forall c, ConstType n (open_tm_wrt_co B (g_Var_f c))) ->
     ConstType (A_Co :: n) (a_CPi phi B).
*)




Inductive arg_targ : pattern_arg -> pattern_arg -> Prop :=
  | AT_Role  : forall R a, 
      arg_targ (p_Tm (Role R) a) (p_Tm (Role R) a)
  | AT_Irrel :forall a, 
      arg_targ (p_Tm (Rho Irrel) a_Bullet) (p_Tm (Rho Irrel) a) 
  | AT_Rel   : forall a,
      arg_targ (p_Tm (Rho Rel) a) (p_Tm (Rho Rel) a)
  | AT_Co    : arg_targ (p_Co g_Triv) (p_Co g_Triv) 
.


Lemma ValuePath_apply_pattern_args : forall args hd F,
  ValuePath (apply_pattern_args hd args) F ->
  ValuePath hd F.
Proof.
  induction args; intros; simpl in *.
  auto.
  destruct a.
  specialize (IHargs _ _  H).
  inversion IHargs.
  auto.
  specialize (IHargs _ _  H).
  inversion IHargs.
  auto.
Qed.


Lemma tm_subst_tm_tm_apply_pattern_args : forall args a0 x a,
   tm_subst_tm_tm a0 x (apply_pattern_args a args) = 
   apply_pattern_args (tm_subst_tm_tm a0 x a) 
                      (List.map (tm_subst_tm_pattern_arg a0 x) args).
Proof. 
  induction args; intros; simpl.
  auto.
  destruct a; simpl.
  rewrite IHargs; auto.
  rewrite IHargs; auto.
Qed.

Definition arg_agree : pattern_arg -> pattern_arg -> Prop :=
  fun arg pat => 
    match (arg,pat) with 
    | (p_Tm nu1 a, p_Tm nu2 p) => nu1 = nu2 /\ tm_pattern_agree a p 
    | (p_Co _, p_Co _) => True
    | (_,_) => False
    end.




(*
Lemma BaseType_cps : forall A sub,
   BaseType A -> 
   BaseType (chain_pattern_substitution A sub).
Proof. 
  intros.
  inversion H.
Admitted.
*)

(*

Invariants about the IH:
   m = length sub   << # we have already opened >>
   n = length args2 << # we still need to open >>  


   tm_pattern_agree (args1 ++ args2) (pargs1 ++ pargs2)

   arg_agree args1 targs1
   arg_agree args2 targs2

   scrut = hd @ args1  @ args2
   pat   = hd @ pargs1 @ pargs2

     |= pargs1 : G1
  

 We will call this lemma with 
    args1 = nil       targs1 == appropriate for args 
    args2 = args      targs2 == nil
    pargs1 = nil      G1 = nil
    pargs2 = pargs 
*)

(* For roles, we need to know that the non-nominal prefix of args 
   matches the Roles for F. 
 *)

Lemma BranchTyping_lemma : forall F n G1 G R A scrut hd pargs1 B0 B1 C,
    BranchTyping (G1 ++ G) n R scrut A hd pargs1 B0 B1 C ->
    forall args1 args2 , 
    map_arg_app args2 = n ->
    forall Rs, RolePath (apply_pattern_args hd args1) F (args_roles args2 ++ Rs) ->
    scrut = apply_pattern_args (apply_pattern_args hd args1) args2  ->
    forall targs1 sub, 
    sub = zip (map fst G1) (rev targs1) ->
    forall B0' targs2,
    open_telescope G n B0' args2 targs2 A ->
    DefEq G (dom G) B0' (chain_pattern_substitution B0 sub) a_Star Rep ->
    apply_pattern_args hd args1 = 
    chain_pattern_substitution (apply_pattern_args hd pargs1) sub ->
    Typing G (apply_pattern_args hd args1) B0' ->
    forall b1' b1,
    b1' = apply_pattern_args b1 (map degrade args2) ->
    Typing G b1 (chain_pattern_substitution B1 sub) ->
    domFresh G1 (fv_tm_tm_tm A) ->  (* TODO: add more fresheness constraints *)
    Typing G (a_CApp b1' g_Triv) C.
Proof.
  intros F n. induction n.
  + intros. inversion H. subst.
    clear H.
    destruct args2; inversion H0. simpl in *.
    with open_telescope do ltac:(fun h => inversion h).
    subst.
    set (s := zip (map fst G1) (rev targs1)) in *.
    with (Typing _ _ (chain_pattern_substitution (a_CPi _ _) _)) 
       do ltac:(fun h => rewrite cps_CPi in h; simpl in h).
    replace (open_tm_wrt_co C0 (g_Var_f c)) with 
            (open_tm_wrt_co C0 g_Triv). 2: { admit. }

    replace (chain_pattern_substitution C0 s) with C0 in  H9.
        2: { admit. }
    eapply E_CApp; eauto 1.
    with (apply_pattern_args _ _ = _) do ltac: (fun h => rewrite <- h).  
    replace (chain_pattern_substitution (apply_pattern_args hd args1)
      s) with (apply_pattern_args hd args1).  2: { admit. } 
    autoreg.
    eapply E_Refl; eauto 1.
    eapply E_Conv; eauto 1.
  + intros.
    destruct args2; inversion H0. simpl in *. 

    set (args1' := (args1 ++ [p])) in *.
    set (targs1' :=  (targs1 ++ [p])) in *.

    with BranchTyping do ltac:(fun h => inversion h; subst; clear h).
    ++ (* Role argument *) 
    destruct p; try destruct nu; simpl in *; try discriminate.
    match goal with [H : A_Tm _ = _ |- _ ] => inversion H; subst end.

    autofresh.
    set (G1' := (x, Tm A0) :: G1) in *.
    set (sub' := (zip (map fst G1') (rev targs1'))) in *.

    with (Typing _ _ (chain_pattern_substitution _ _)) do 
         ltac:(fun h => rewrite cps_Pi in h).
    with (DefEq _ _ _ (chain_pattern_substitution _ _)) do 
         ltac:(fun h => rewrite cps_Pi in h).

    with (open_telescope) do ltac:(fun h => inversion h; subst; clear h).

    have SA: chain_pattern_substitution (a_Var_f x) sub' = a.
    admit.

    with BranchTyping do ltac:(fun h =>
        specialize (IHn G1' G _ _ _ _ _ _ _ _ h); clear h).  

    specialize (IHn  args1' args2 eq_refl Rs). 
    rewrite apply_pattern_args_tail_Tm in IHn.

    lapply IHn. clear IHn. move=> IHn. 2 : {
      econstructor; eauto using Typing_lc1.
    }

    specialize (IHn eq_refl).

    specialize (IHn targs1' sub' eq_refl).

    with (open_telescope) do 
         ltac:(fun h => specialize (IHn _ _ h); clear h).

    lapply IHn. clear IHn. move=>IHn. 2: {
      eapply E_Trans with (a1 := open_tm_wrt_tm B0 a); eauto 1.
      rewrite cps_open_tm_wrt_tm.       
      admit. (* lc *)
      rewrite SA.
      unfold sub'. unfold G1'. unfold targs1'.
      rewrite rev_unit.
      simpl.

      rewrite tm_subst_tm_tm_fresh_eq. admit.
      eapply E_PiSnd; eauto 1.
      eapply E_Refl; eauto using Typing_lc1.
    }

    simpl in IHn.

    have next: a_App (apply_pattern_args hd args1) (Role R) a =
        chain_pattern_substitution
          (apply_pattern_args (a_App hd (Role R) (a_Var_f x)) pargs1) sub'.
    admit. 
    specialize (IHn next). clear next.

    lapply IHn. clear IHn. move=> IHn. 2: {
      eapply E_Conv; eauto 1. 2: { eapply E_Sym; eauto 1. }
      eapply E_TApp; eauto 1.
      { autoreg. auto. }
    }

    eapply IHn. eauto.

    rewrite cps_open_tm_wrt_tm.
    admit. (* lc *)
    rewrite SA.
    eapply E_App; eauto 1.
    eapply E_Conv; eauto 1.
    admit. admit.
    unfold G1'. unfold domFresh.
    econstructor. unhide Fr. auto. auto.
    ++ (* Rho Rel *) admit.
    ++ (* Rho Irrel *) admit.
    ++ (* Co *) admit.
Admitted.

(* Specialized version of main lemma that is "easier" to use. *)
Lemma BranchTyping_start : forall  G n R A scrut hd B0 B1 C F,
    BranchTyping G n R scrut A hd nil B0 B1 C ->
    forall args, map_arg_app args = n ->
    forall Rs, RolePath hd F (args_roles args ++ Rs) ->
    scrut = apply_pattern_args hd args  ->
    forall B0' targs,
    open_telescope G n B0' args targs A ->
    DefEq G (dom G) B0' B0 a_Star Rep ->
    Typing G hd B0' ->
    forall b1' b1,
    b1' = apply_pattern_args b1 (map degrade args) ->
    Typing G b1 B1  ->
    Typing G (a_CApp b1' g_Triv) C.
Proof.
  intros.
  eapply BranchTyping_lemma with (G1 := nil)(args1 := nil)
                                 (pargs1:=nil)(targs1:=nil); eauto 1. 
  unfold domFresh. eauto.
Qed.


Lemma rev_injective : forall A (xs ys : list A), rev xs = rev ys -> xs = ys.
Proof.
  induction xs. intros. destruct ys; simpl in H; inversion H; auto.
  move: (app_cons_not_nil (rev ys) nil a) => h0. contradiction.
  intros. 
  destruct ys; simpl in H; inversion H; auto.
  move: (app_cons_not_nil (rev xs) nil a) => h0. rewrite H1 in h0. contradiction.
  apply app_inj_tail in H.
  destruct H.
  f_equal; auto.
Qed.


Lemma shuffle : forall A (args : list A) a rargs,
(a :: rargs = rev args) -> args = rev rargs ++ [a].
Proof.
  intros. 
  rewrite <- (rev_involutive rargs) in H.
  rewrite <- rev_unit in H.
  apply rev_injective in H.
  auto.
Qed.

Lemma map_arg_app_snoc : forall args App,
    map_arg_app (args ++ [App]) = A_snoc (map_arg_app args) (arg_app App).
Proof.
  induction args.
  simpl. eauto.
  intros. simpl. rewrite IHargs. eauto.
Qed.
  
Lemma AppsPath_arg_app' : forall rargs args, rargs = rev args -> forall n R F,
  AppsPath R (apply_pattern_args (a_Fam F) args) F n -> 
  map_arg_app args = n.
Proof.
  induction rargs.
  - intros. destruct args; simpl in H; inversion  H. 
    simpl in *. inversion H0; auto.
    apply app_cons_not_nil in H. contradiction.
  - intros args H n R F AP.
    apply shuffle in H.
    rewrite H in AP.
    destruct a; try destruct nu.
    all: try rewrite apply_pattern_args_tail_Tm in AP.    
    all: try rewrite apply_pattern_args_tail_Co in AP.    
    all: inversion AP; subst.
    all: rewrite map_arg_app_snoc; f_equal;
      eapply IHrargs; eauto. 
    all: rewrite rev_involutive; auto.
Qed.

Lemma AppsPath_arg_app : forall args n R F,
  AppsPath R (apply_pattern_args (a_Fam F) args) F n -> 
  map_arg_app args = n.
Proof.
  intros args. intros.
  eapply (@AppsPath_arg_app' (rev args) args eq_refl).
  eauto.
Qed.

Lemma RolePath_args : forall F Rs, 
    RolePath (a_Fam F) F Rs ->
    forall args Rs', RolePath (apply_pattern_args (a_Fam F) (rev args)) F Rs' ->
    Rs = (args_roles (rev args)) ++ Rs'.
Proof.
  intros F Rs RP.
  induction args; intros Rs' RP'.
  - simpl in *. 
    inversion RP; inversion RP'; subst.
    all: move: (binds_unique _ _ _ _ _ H0 H4 uniq_toplevel) => EQ; inversion EQ.
    all: auto.
  - simpl in *.
    destruct a; try destruct nu; try destruct rho.
    all: try rewrite apply_pattern_args_tail_Tm in RP'.
    all: try rewrite apply_pattern_args_tail_Co in RP'.
    all: inversion RP'; subst; simpl. clear RP'.
    all: with RolePath do ltac:(fun h => move: (IHargs _ h) => eq).
    all: subst; simpl.
    all: rewrite args_roles_app; simpl.
    all: rewrite <- app_assoc; simpl; auto.
Qed.

Lemma RolePath_AppRole : 
    forall args Rs, AppRoles (map_arg_app args) Rs -> 
    forall hd F,  RolePath hd F Rs ->
    Rs = args_roles args.
Proof.
  intros args Rs H. dependent induction H; eauto.
  + intros. destruct args; inversion x. simpl. auto. 
  + intros. destruct args; inversion x. subst. 
    destruct p; try destruct nu; inversion H2; subst.
    simpl. erewrite IHAppRoles; eauto.
  + intros. destruct args; inversion x. subst. 
    destruct p; try destruct nu; inversion H2; subst.
    simpl. erewrite IHAppRoles; eauto.
  + intros. destruct args; inversion x. subst. 
    destruct p; try destruct nu; inversion H2; subst.
    simpl. erewrite IHAppRoles; eauto.
Unshelve. all: eauto.
Qed.

Lemma BranchTyping_preservation : forall G n R a A F B0 B1 C,
    BranchTyping G n R a A (a_Fam F) nil B0 B1 C ->
    CasePath R a F ->
    AppsPath R a F n ->
    SatApp F n ->
    Typing G a A ->
    Typing G (a_Fam F) B0 ->
    forall b1, Typing G b1 B1 ->
    forall b1', ApplyArgs a b1 b1' ->
    Typing G  (a_CApp b1' g_Triv) C.
Proof.
  intros G n R a A F B0 B1 C BT CP AP SA Ta Tp b1 Tb1 b1' AA.
  have VP:  ValuePath a F.   
  eapply ett_path.CasePath_ValuePath; eauto.
  edestruct ApplyArgs_pattern_args as [args [h0 h1]]; eauto 1.
  subst a.
  move: (invert_Typing_pattern_args2 _ _  Ta) => [PiB [targs [h2 h4]]].
  
  have eq: map_arg_app args = n.  eapply AppsPath_arg_app; eauto.
  rewrite eq in h2.

  have RP: RolePath (a_Fam F) F (args_roles args).
  { inversion SA. subst.
    ++ replace (args_roles args) with Rs. 
       eauto. eapply RolePath_AppRole; eauto.
    ++ replace (args_roles args) with Rs. 
       eauto. eapply RolePath_AppRole; eauto.
       rewrite eq. auto.
  }     
  eapply BranchTyping_start with (Rs := nil); eauto 1.
  rewrite app_nil_r; eauto.
  eapply Typing_a_Fam_unique; eauto 1.
Qed.

(* --------------------------------------------------------- *)

(*
Lemma MatchSubst_args :
  forall a p b b' (ms : MatchSubst a p b b'),
    exists args, chain_pattern_substitution b args = b'.
Proof.
  induction 1.
  exists nil. simpl. eauto.
  all: move: IHms => [args h].
  all: try solve [eauto].
  exists ((x, p_Tm (Rho Rel) a)::args). simpl. rewrite h. auto.
Qed.
*)

(*
(* Need to also say that vars P # C *)
Definition patternFresh p s :=
  AtomSetImpl.inter (of_list (vars_Pattern p)) s [<=] empty.


Lemma MatchSubst_refl : forall p, 
    ett_match.Pattern p ->
    forall C, lc_tm C -> 
    MatchSubst p p C C.
Proof. 
  induction 1; intros; eauto.
  rewrite <- (tm_subst_tm_tm_id x).
  eapply MatchSubst_AppRelR; eauto.
Qed.
*)

(*
Definition sub := list (atom * tm). *)

(* MatchTyping describes the relationship between the pattern 
   and the scrutinee during type checking

   If we have

     MatchTyping Gp p B G a A sub 

   then 

     Gp |= p : B
     G  |= a : A

   and

     chain_pattern_substitution (zip (fst Gp) sub) p = a 
     chain_pattern_substitution (zip (fst Gp) sub) B = A
   
*)
Inductive MatchTyping : 
  context -> tm -> tm -> context -> tm -> tm -> list pattern_arg -> Prop := 
  | MatchTyping_Const : forall G F PiB B,
    Typing G (a_Fam F) PiB ->
    DefEq G (dom G) PiB B a_Star Rep ->
    MatchTyping nil (a_Fam F) PiB G (a_Fam F) B nil
  | MatchTyping_AppRelR : 
    forall G Gp R p x A1 B1 a1 a2 A2 B2 A sub,
    MatchTyping Gp p (a_Pi Rel A1 B1) G a1 (a_Pi Rel A2 B2) sub ->
    Typing G a2 A2 ->
    DefEq G (dom G) A (open_tm_wrt_tm B2 a2) a_Star Rep ->
    MatchTyping (x ~ Tm A1 ++ Gp)
                (a_App p  (Role R) (a_Var_f x)) (open_tm_wrt_tm B1 (a_Var_f x))
                G  (a_App a1 (Role R) a2)          A
                ((p_Tm (Role R) a2) :: sub) 
  | MatchTyping_AppIrrel : 
    forall Gp G p x A1 B1 a1 a2 a2' A2 B2 A sub,
    MatchTyping Gp p (a_Pi Irrel A1 B1) G a1 (a_Pi Irrel A2 B2) sub ->
    Typing G a2' A2 ->
    DefEq G (dom G) A (open_tm_wrt_tm B2 a2') a_Star Rep ->
    MatchTyping (x ~ Tm A1 ++ Gp)
                (a_App p  (Rho Irrel) a_Bullet) (open_tm_wrt_tm B1 (a_Var_f x))
                G (a_App a1 (Rho Irrel) a2)       A
                ((p_Tm (Rho Irrel) a2) :: sub) 
  | MatchTyping_CApp : 
    forall Gp G c p phi1 B1 a1 phi2 B2 A sub,
    MatchTyping Gp p (a_CPi phi1 B1) G a1 (a_CPi phi2 B2) sub ->
    DefEq G (dom G) A (open_tm_wrt_co B2 g_Triv) a_Star Rep ->
    MatchTyping (c ~ Co phi1 ++ Gp) (a_CApp p  g_Triv) 
                (open_tm_wrt_co B1 (g_Var_f c))
                G (a_CApp a1 g_Triv) A
                (p_Co g_Triv :: sub)
.


Lemma PaternPath_MatchTyping : forall a p, 
   tm_pattern_agree a p ->
   `{ PatternContexts Ωp Gp F PiB p B ->
      Typing G (a_Fam F) PiB ->
      ValuePath a F ->
      G ⊨ a : A →
      exists sub, MatchTyping Gp p B G a A sub}.
Proof.
  induction 1; intros.
  all: with PatternContexts do ltac:(fun h => inversion h).
  all: subst.
  - exists nil. econstructor; eauto 2.
    eapply Typing_a_Fam_unique; eauto 1.
  - with ValuePath do ltac: (fun h => inversion h; subst). 
    move: (invert_a_App_Role H4) => [A1 [B1 h]]. split_hyp.
    edestruct IHtm_pattern_agree as [s h]; eauto 1. 
    eexists. econstructor; eauto 1.
  - with ValuePath do ltac: (fun h => inversion h; subst). 
    move: (invert_a_App_Irrel H4) => [A1 [B1 [b0 h]]]. split_hyp.
    edestruct IHtm_pattern_agree as [s h]; eauto 1. 
    eexists. econstructor; eauto 1.
  - with ValuePath do ltac: (fun h => inversion h; subst). 
    move: (invert_a_CApp H3) => [a2 [b2 [A2 [A3 [R1 [B0 h]]]]]]. split_hyp.
    edestruct IHtm_pattern_agree as [s h]; eauto 1. 
    eexists. econstructor; eauto 1.
Qed.

(*
Lemma MatchTyping_correctness1 : 
  `{ MatchTyping Gp p B G a A s ->
     domFresh Gp (fv_tm_tm_tm a) ->
     NoDup (map fst s) ->
     chain_substitution p s = a }.
Proof.
  induction 1; intros; simpl; auto.
  rewrite chain_subst_app. simpl.
  apply domFresh_cons in H2. split_hyp. simpl in H4.
  apply domFresh_union in H4. split_hyp.
  simpl in *.
  with NoDup do ltac:(fun h => inversion h) end; subst.
Admitted.
*)

Lemma MatchTyping_correctness2 : 
  `{ MatchTyping Gp p B G a A s ->
     domFresh Gp (dom G) ->
     G ∥ dom G ⊨ chain_pattern_substitution B (zip (map fst Gp) s) ∼ A : a_Star / Rep }.
Proof.
  induction 1.
  + intros; simpl; auto.
  + intros; simpl in *.
(*     with NoDup do ltac:(fun h => inversion h; clear h). subst. *)
    apply domFresh_cons in H2. split_hyp. clear H2.
(*    simpl_env in H3.
    apply domFresh_cons in H3. split_hyp.  *)
    specialize (IHMatchTyping ltac:(auto)). 
    rewrite cps_Pi in IHMatchTyping.
    set (s := zip (map fst Gp) sub) in *.
    have EA: DefEq G (dom G) (chain_pattern_substitution A1 s) A2 a_Star Rep.
    { eapply E_PiFst; eauto 1. }
    erewrite cps_cons_Tm.  
    have EQ1: forall nu, chain_pattern_substitution 
                (open_tm_wrt_tm B1 (a_Var_f x)) ((x, p_Tm nu a2) :: s) = 
              (open_tm_wrt_tm (chain_pattern_substitution B1 ((x,p_Tm (Rho Rel) a2)::s)) a2).
    { intro nu. rewrite cps_open_tm_wrt_tm. admit. (* lc *)
      f_equal.
      rewrite cps_subst_var; auto.
      admit.
    } 
    erewrite EQ1.
    eapply E_Trans; eauto 1. 2: { eapply E_Sym. eauto 1. }
    
    have EQ2: chain_pattern_substitution B1 ((x, p_Tm (Rho Rel) a2) :: s) = 
              chain_pattern_substitution B1 s.
    { admit. }
    rewrite EQ2. 
    eapply E_PiSnd; eauto 1.
    eapply E_Refl; eauto 1.
    eapply E_Conv; eauto 1. eapply E_Sym; eauto 1.
    autoreg. auto.
  + admit.
  + admit.
Admitted.

    (* 

   MatchSubst a p b b'
   is defined outside-in on the pattern p 
       in conjunction with the path a
   at each step, if p has type B then 
       a has type (chain_substiution_args B targs)
       where sub are the type arguments 
       corresponding to the earlier arguments
  
*)



Lemma Ctx_app : forall G1,  Ctx G1 -> forall G2, uniq(G1 ++ G2) -> Ctx G2 -> Ctx (G1 ++ G2).
Proof. 
  induction G1; intros; auto. 
  simpl_env in *. 
  inversion H0. subst.
  inversion H; subst.
  + econstructor; eauto 3.
    specialize (Typing_weakening H8 G2 G1 nil) => WK.
    rewrite! app_nil_r in WK.
    apply WK; eauto 3.
  + econstructor; eauto 3.
    specialize (PropWff_weakening H8 G2 G1 nil) => WK.
    rewrite! app_nil_r in WK.
    apply WK; eauto 3.
Qed.

Lemma MatchSubstTyping :  `{
  forall a p b b' (ms : MatchSubst a p b b'),
  forall Gp G A B sub, 
    MatchTyping Gp p B G a A sub ->
  forall C Gp2, 
    uniq (Gp2 ++ G) ->
    (Gp2 ++ Gp ⊨ b : C) ->
    (cps_context Gp2 (zip (map fst Gp) sub) ++ G ⊨ b' : 
          chain_pattern_substitution C (zip (map fst Gp) sub)) 
}.
Proof.
  induction 1; intros.
  all: with MatchTyping do ltac:(fun h => inversion h; subst; clear h).
  - simpl in *. 
    have EQ: cps_context Gp2 ∅ = Gp2.
    { generalize Gp2. induction Gp0. simpl. auto.
      simpl. destruct a. rewrite IHGp0. f_equal.
      f_equal. apply cps_sort_nil. }
    rewrite EQ.
    with (Typing _ b _) do ltac:(fun h => 
        specialize (Typing_weakening h G Gp2 nil eq_refl)) end.
    move=> WK. rewrite app_nil_r in WK. apply WK.
    rewrite app_nil_r in H2.
    eapply Ctx_app; eauto using Typing_Ctx.

  - with MatchTyping do ltac:(fun h =>
         specialize (IHms Gp0 G _ _ sub0 h C); clear h) end.
    rewrite app_assoc in H2.
    have U: uniq ((Gp2 ++ x ~ Tm A1) ++ G). admit. 
       (* Need additional freshness about Gp *)
    specialize (IHms _ U H2). 
    unfold cps_context in *.
    rewrite EnvImpl.map_app in IHms.
    unfold one in IHms.
    simpl in IHms.
    set (s := (zip (map fst Gp0) sub0)).
    have EQ: A2 = chain_pattern_substitution A1 s. admit.
    rewrite EQ in H14.
    destruct tm_substitution_mutual as [L _].
    specialize (L _ _ _ IHms).
    specialize (L _ _ _ H14).
    specialize (L (cps_context Gp2 s) x).
    lapply L. clear L. move=>L. 2: {
      simpl_env.
      f_equal.
    }    
    have EQ3: utils.map = EnvImpl.map. auto. rewrite EQ3 in L.
    have EQ4:
       EnvImpl.map (tm_subst_tm_sort a x) (cps_context Gp2 s) = 
       EnvImpl.map (cps_sort^~ (x ~ (p_Tm (Rho Rel) a) ++ s)) Gp2.
    { 
      generalize Gp2.
      induction Gp1.
      simpl. auto.
      simpl. destruct a0. rewrite IHGp1.
      f_equal. f_equal. eapply cps_sort_cons.
    }
    rewrite EQ4 in L.
    have EQ5:
      tm_subst_tm_tm a x (chain_pattern_substitution C s) = 
      chain_pattern_substitution C (x ~ (p_Tm (Rho Rel) a) ++ s).
    {
      eapply cps_cons_Tm.
    } 
    rewrite EQ5 in L.
    eapply L.
  - admit.
  - admit.
Admitted.


Lemma MatchSubstTyping_start :  `{
  forall a p b b' (ms : MatchSubst a p b b'),
  forall Gp G A B sub, MatchTyping Gp p B G a A sub ->
  domFresh Gp (dom G) ->
  G ⊨ A : a_Star -> 
  (Gp ⊨ b : B) ->
  (G ⊨ b' : A) 
}.
Proof.
  intros.
  move: (MatchSubstTyping ms H) => h0.
  specialize (h0 B nil ltac:(eapply Ctx_uniq; eapply Typing_Ctx; eauto) ltac:(auto)).   simpl in h0.
  eapply E_Conv; eauto 1.
  eapply MatchTyping_correctness2; eauto 1.
Admitted.

Theorem MatchSubst_preservation2 : `{
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
  move: (Typing_regularity tpg_a) => tpg_A.


  (* new stuff *)
  edestruct PaternPath_MatchTyping as [sub0 h]; eauto 2.
  admit.
  admit.
  eapply MatchSubstTyping_start; eauto.
  admit.
Admitted.


(* -------------------------------------------------------- *)


Lemma Beta_preservation : `(Beta a b R →  forall G A, Typing G a A -> Typing G b A).
Proof.
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
   - (* Axiom *)
     eapply MatchSubst_preservation; eauto.
   - (* Pattern True *)
     move: (invert_a_Pattern TH) => [A [A1 [B0 [C h]]]].
     split_hyp.
     eapply E_Conv with (A := C); eauto 1.
     eapply BranchTyping_preservation; eauto 1.
     eauto using AppsPath_CasePath.
     autoreg. auto.
   - dependent induction TH; eauto.
Qed.


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
  - apply toplevel_inversion in H.
    (*
    autofwd.
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

