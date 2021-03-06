(* Definition and facts about patterns *)

Require Import FcEtt.imports.
Require Import FcEtt.tactics.
Require Import FcEtt.notations.
Require Import FcEtt.utils_fun.

Require Import FcEtt.ett_ott.

(* FIXME: temporary *)
Generalizable All Variables.

(* TODO: technically, `Pattern a` only says that a is a pattern-like term. 
   Better terminology..? `PatternShape` maybe? *)

(* Basic tactic to solve obligations generated by the definition of partial 
   functions (with Program) *)
(* Note: be sure to bind any invertible hypothesis as H, so that they gets 
   inverted (it's certainly hacky
   to rely on the naming, but (simple) principled solutions tend to be 
   notably slower) *)
Ltac partial_fun_def_solve :=
  Tactics.program_simpl;
  try solve
    [inversion H; try (by subst);
       match goal with | [H : _ |- _] => solve [eapply H; by eassumption] end
    | repeat split; intros; discriminate
    | cbn; match goal with | [H : _ |- _] => by invs H end].

Fixpoint fv_tm_args args :=
  match args with
    | [] => empty
    | h :: tl => (
      match h with
        | p_Tm nu t => fv_tm_tm_tm t
        | p_Co g    => fv_tm_tm_co g
      end) `union` fv_tm_args tl
  end.

(* TODO: unify with head_const in ett_match.v (should use this version) *)
Fixpoint pat_head (p : tm) : option const :=
  match p with
    | a_Fam F       => Some F
    | a_App a' nu b => pat_head a'
    | a_CApp a' g   => pat_head a'
    | _             => None
  end.

(* TODO: unify with ett_match.v (should use this version) *)
(* TODO: default or option type? *)
Fixpoint pat_args_default (p : tm) : pattern_args :=
  match p with
    | a_Fam F          => []
    | a_App a' nu b    => p_Tm nu b :: pat_args_default a'
    | a_CApp a' g      => p_Co g    :: pat_args_default a'
    | _                => []
  end.

Lemma SubPat_pat_head: `{SubPat p1 p2 → pat_head p1 = pat_head p2}.
Proof.
  intros until 0.
  move=> spat.
  dependent induction spat; intros; ok.
Qed.

Lemma SubPat_Pattern_1: `{SubPat p1 p2 → Pattern p1}.
Proof.
  induction 1; eauto.
Qed.

Lemma SubPat_Pattern_2: `{SubPat p1 p2 → Pattern p2}.
Proof.
  induction 1; eauto.
Qed.

Program Fixpoint tm_pattern_agree_Pattern_1 a : forall p, tm_pattern_agree a p → Pattern a :=
  fun p H =>
  match a with
    | a_Fam F                => Pattern_Head F
    (* TODO: the second match only serves to deduce the shape of p and bind p'.
             Could it be done in a nicer manner? (less verbose in particular) *)
    | a_App a' (Role R) b    => match p with | a_App p' _ _ => Pattern_Rel a' R b _ (@tm_pattern_agree_Pattern_1 a' p' _) | _ => False_rect _ _ end
    | a_App a' (Rho Irrel) b => match p with | a_App p' _ _ => Pattern_Irrel a' b _   (@tm_pattern_agree_Pattern_1 a' p' _) | _ => False_rect _ _ end
    | a_CApp a' g            => match p with | a_CApp p' _  => Pattern_Co a' g _   (@tm_pattern_agree_Pattern_1 a' p' _) | _ => False_rect _ _ end
    | _                      => False_rect _ _
  end.

Solve All Obligations with partial_fun_def_solve.


(* FIXME: technically, JMeq relies on an axiom... *)
Lemma JMeq_eq_tpa : `{forall (pf1 pf2 : tm_pattern_agree a p), JMeq pf1 pf2 -> pf1 = pf2}.
Proof.
  intros.
  eapply JMeq_rect; eauto.
Qed.


Scheme tm_pattern_agree_dep := Induction for tm_pattern_agree Sort Prop.

(* FIXME: weird error here, what's up?
Program Fixpoint tm_pattern_agree_uniqueness  {a p} (pf1 pf2 : tm_pattern_agree a p) : pf1 = pf2 :=
  match pf1, pf2 with
    | tm_pattern_agree_Const _, tm_pattern_agree_Const _ => _
    | tm_pattern_agree_AppRelR _ _ _ _ _ _ _, tm_pattern_agree_AppRelR _ _ _ _ _ _ _ => _
    | tm_pattern_agree_AppIrrel _ _ _ _ _, tm_pattern_agree_AppIrrel _ _ _ _ _ => _
    | tm_pattern_agree_CApp _ _ _, tm_pattern_agree_CApp _ _ _ => _
    | _, _ => False_rect _ _ 
  end.
*)

Lemma tm_pattern_agree_uniqueness : `{forall (pf1 pf2 : tm_pattern_agree a p), pf1 = pf2}.
Proof.
(* FIXME: old proof attempts for reference *)
(*
  set (P := fun a1 p1 (pf1 : tm_pattern_agree a1 p1) => forall a2 p2 (pf2 : tm_pattern_agree a2 p2) (eq1 : JMeq a2 a1) (eq2 : JMeq p2 p1), JMeq pf1 pf2).
  suff: 
    forall a1 p1 (pf1 : tm_pattern_agree a1 p1) a2 p2 (pf2 : tm_pattern_agree a2 p2) (eq1 : JMeq a2 a1) (eq2 : JMeq p2 p1),
    JMeq pf1 pf2
  by intros; eapply JMeq_eq_tpa; eapply x.
  refine (tm_pattern_agree_dep P _ _ _ _); unfold P; intros.
  destruct eq1.
  rewrite eq1 in pf2.
  in



  move: tm_pattern_agree_dep.
  move/(_ P).
  intros ?? pf1.
  eapply tm_pattern_agree_dep; intros. Check tm_pattern_agree_dep.
  - exact pf1.
  - move: H.
    move/(_ _ _ pf2).
    apply; eassumption.
  - move: H.
    move/(_ _ _ pf2).
    apply; eassumption.
  - move: H.
    move/(_ _ _ pf2).
    apply; eassumption.
  - 

  try inversion pf1;
  destruct p;
  try inversion pf1; 
  intros; subst.
*)
Admitted.

Lemma tm_pattern_agree_Pattern_1_proofirr: `{
  @tm_pattern_agree_Pattern_1 a p pf1 = @tm_pattern_agree_Pattern_1 a p pf2}.
Proof.
  intros.
  by rewrite (tm_pattern_agree_uniqueness pf1 pf2).

  (* FIXME: Old proof attempt. Technically, this lemma is true even without tm_pattern_agree_uniqueness,
     but it obviously makes the proof much easier.
     Keeping this here just in case tm_pattern_agree_uniqueness can't be proved,
     as tm_pattern_agree_Pattern_1_proofirr might nonetheless be provable *)
  (*
  induction a; intros; try by cbn; try by inversion pf1.
  destruct nu; destruct p; inversion pf1; try done. destruct pf1; cbn.
  rewrite IHa1. cbn. ok.
  *)
Admitted.

(* TODO: adapt like tm_pattern_agree_Pattern_1 *)
Lemma tm_pattern_agree_Pattern_2 : `{tm_pattern_agree a p → Pattern p}.
Proof.
  induction 1; eauto.
Defined.

Hint Resolve SubPat_Pattern_1 SubPat_Pattern_2 tm_pattern_agree_Pattern_1 tm_pattern_agree_Pattern_2.

Lemma pat_args_default_fv : `{
  Pattern a →
  fv_tm_tm_tm a [=] fv_tm_args (pat_args_default a)}.
Proof.
  induction 1; cbn; ok.
Qed.

Lemma MatchSubst_Pattern_1 : `{
  MatchSubst a p b1 b2 →
  Pattern a}.
Proof.
  induction 1; eauto.
Qed.

Lemma MatchSubst_Pattern_2 : `{
  MatchSubst a p b1 b2 →
  Pattern p}.
Proof.
  induction 1; econstructor; eauto. (* eauto alone gets lost *)
Qed.

Hint Resolve MatchSubst_Pattern_1 MatchSubst_Pattern_2.

Lemma Rename_pat_head : `{
  Rename p b p' b' s s' →
  pat_head p = pat_head p'
}.
Proof.
  induction 1;
  try invs H;
  ok.
Qed.

Lemma Rename_Pattern : `{
  Rename p b p' b' s s' →
  Pattern p /\ Pattern p'
}.
Proof.
  (* FIXME: currently not true, since Rename doesn't allow irrelevant arguments to
            appear in a pattern.

  induction 1; ok.
Qed. *)
Admitted.

Lemma Rename_spec : `{
  Rename p b p' b' s s' →
  fv_tm_tm_tm p' ∩ (s ∪ s') [=] empty /\ fv_tm_tm_tm b' ∩ (s ∪ s') [=] empty
}.
Proof.
  induction 1.
  - admit. (* FIXME: as of this revision, the definition of Rename seems wrong (base case) *)
  - (* FIXME: taking forever *)
Admitted.

Lemma Rename_PatCtx_Typing_exist: `{
  Rename p b p' b' s s' →
  PatternContexts Ω Γ F PiB p B →
  Γ ⊨ b : B →
   ∃ Ω' Γ' B',
  PatternContexts Ω' Γ' F PiB p' B' /\ Γ' ⊨ b' : B'
}.
Proof.
  (* TODO: this might be proved somewhere else already *)
Admitted.

Lemma PatternContexts_pat_head : `{
  PatternContexts Ω Γ F PiB p B →
  pat_head p = Some F}.
Proof.
  induction 1; ok.
Qed.

Lemma binds_toplevel_pat_head : `{binds F (Ax p b PiB R Rs) toplevel → pat_head p = Some F}.
Proof.
  introfwd.
  (* TODO: sig toplevel + use PatternContexts_pat_head *)
Admitted.


Lemma binds_toplevel_Pattern: `{binds F (Ax p b PiB R Rs) toplevel → Pattern p}.
Proof.
  introfwd.
Admitted.

(* FIXME: might exist somewhere else *)
Lemma Rename_subset : `{
  Rename p b p' b' s s' →
   ∀ s'', s'' ⊂ s →
  Rename p b p' b' s'' s'
}.
Proof.
  induction 1; intros; ok.
Admitted.



(******** Substitution of a list of arguments ********)

(* In the following, the context provides the names of the variables to be substituted. *)

Fixpoint subst_args_in_term Γ args A :=
  match Γ, args with
    | h1 :: t1, h2 :: t2 =>
      (* TODO: put this part in its own function *)
      match h1, h2 with
        | (x, Tm _ ), p_Tm _ a => tm_subst_tm_tm a x (subst_args_in_term t1 t2 A)
        | _, _ => A
      end
    | _, _ => A
  end.

(*
Definition subst_args_in_sort Γ args S :=
  match S with
    | Tm A => Tm (subst_args_in_term Γ args A)
    | Co g => Co g (* TODO *)
  end.
  *)

Fixpoint subst_args_in_sort Γ args S :=
  match Γ, args with
    | h1 :: t1, h2 :: t2 =>
      match h1, h2 with
        | (x, Tm _ ), p_Tm _ a => tm_subst_tm_sort a x (subst_args_in_sort t1 t2 S)
        | _, _ => S
      end
    | _, _ => S
  end.


Definition subst_args_in_ctx Γ args : context → context := map_r (subst_args_in_sort Γ args).

Fact subst_args_in_ctx_app: `{
  subst_args_in_ctx Γ args (Γ1 ++ Γ2) = (subst_args_in_ctx Γ args Γ1) ++ (subst_args_in_ctx Γ args Γ2)
}.
Proof.
  intros.
  unfold subst_args_in_ctx; unfold map_r.
  admit.  (* by rewrite map_app. *)
Admitted. 

Hint Rewrite @subst_args_in_ctx_app : extended_comp.

Fact subst_args_in_term_a_Pi : `{
  subst_args_in_term Γ args (a_Pi ρ A B) = a_Pi ρ (subst_args_in_term Γ args A) (subst_args_in_term Γ args B)
}.
Proof.
  induction Γ, args; intros; cbn; try done.
  exactly 1 goal.
  rewrite IHΓ. cbn.
  by destruct a, s, p.
Qed.

Fact subst_args_in_sort_Tm : `{
  subst_args_in_sort Γ0 args1 (Tm A') = Tm (subst_args_in_term Γ0 args1 A')   (* FIXME vars *)
}.
Proof.
Admitted.

Fact subst_args_in_ctx_nil : `{
  subst_args_in_ctx ∅ ∅ Γ = Γ
}.
Proof.
  induction Γ; try done; cbn.
  rewrite IHΓ.
  destruct a; reflexivity.
Qed.

Hint Rewrite @subst_args_in_term_a_Pi @subst_args_in_sort_Tm @subst_args_in_ctx_nil : extended_comp.


Hint Constructors PatData. (* TODO: remove, right? *)