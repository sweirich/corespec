Require Import FcEtt.imports.

(* FIXME; instead of importing inf, import only the right metalib module *)
Require Import FcEtt.ett_inf.

Require Import FcEtt.fset_facts.

(* TODO: sort the import, remove unnecessary ones *)
Import AtomSetFacts AtomSetProperties.

Require Import FcEtt.notations.

Require Export FcEtt.tactics_safe.
Require Export FcEtt.tactics_ecomp.

(**** Tactics for the project ****)


(* TODO
   - automated f_equal (etc)
   - split forall ands
   - automatic regularity application (example use sites: fc_dec_fun, ext_red)
   - the organization (in different tactics, etc) is probably perfectible
*)


Module TacticsInternals.
(*******************************)
(**** Basic Building Blocks ****)
(*******************************)

(* Shorthands for instantiation/specialization *)
Ltac spec2 H x xL := specialize (H x xL).
Ltac inst2 H x xL := let h := fresh H x in move: (H x xL) => h.

(* Dynamic type, useful for some tactics *)
Polymorphic (* Cumulative *) Inductive Dyn : Type := dyn : forall {T : Type}, T -> Dyn.

Ltac unwrap_dyn d :=
  match d with
    | dyn ?v => v
  end.


(* TODO: This is subsumed by pcess_hyps down there. Make sure we never need to use *specifically* this tactic, then remove it *)
Ltac split_hyp :=
  repeat (
      match goal with
        | [ H : _ /\ _ |- _ ] => destruct H
      end).



Ltac rewrite_and_clear eq :=
  first [rewrite -> eq | rewrite <- eq]; clear eq.

Ltac try_rewrite_and_clear eq :=
  first [rewrite -> ! eq | rewrite <- ! eq | idtac]; clear eq.

(* Only forward (i.e., ->) *)
Ltac try_rewrite_and_clear_f eq :=
  first [rewrite ! eq | idtac]; clear eq.

(* Integrate these in the big match below? *)
(* Find an generalized equality, rewrite it, and clear it *)
(* TODO: need much more parameters *)
Ltac find_eq_rew_clear :=
  match goal with
    | [ eq : forall t1,                _ = _ |- _ ] => rewrite_and_clear eq
    | [ eq : forall t1 t2,             _ = _ |- _ ] => rewrite_and_clear eq
    | [ eq : forall t1 t2 t3,          _ = _ |- _ ] => rewrite_and_clear eq
    | [ eq : forall t1 t2 t3 t4,       _ = _ |- _ ] => rewrite_and_clear eq
    | [ eq : forall t1 t2 t3 t4 t5,    _ = _ |- _ ] => rewrite_and_clear eq
    | [ eq : forall t1 t2 t3 t4 t5 t6, _ = _ |- _ ] => rewrite_and_clear eq

  end.

Ltac clearall :=
  repeat match goal with
    | [ H : _ |- _ ] => clear H
  end.

(* Tactic equivalent to subst, but which also tries to rewrite universally quantified equalities *)
(* FIXME: better name *)
Ltac subst_forall :=
  repeat find_eq_rew_clear.


Ltac check_num_goals_eq g := let n:= numgoals in guard n=g.


(* Inversion and substitution *)
Ltac invs H := inversion H; subst.

(*****************)
(**** Solvers ****)
(*****************)


(* The <solve> versions are strict: they solve the goal or do nothing. The <nosolve> versions do whatever they can *)

Tactic Notation "basic_nosolve_n"     int_or_var(n) :=
  intuition (subst; eauto n).
Tactic Notation "basic_nosolve_n'"    int_or_var(n) :=
  intuition (subst; simpl in *; subst; eauto n; try done).
Tactic Notation "basic_nosolve_fo_n"  int_or_var(n) :=
  firstorder (subst; eauto n).
Tactic Notation "basic_nosolve_fo_n'" int_or_var(n) :=
  firstorder (subst_forall; simpl in *; subst_forall; eauto n; try done).

Tactic Notation "basic_solve_n"     int_or_var(n) := try solve [basic_nosolve_n     n].
Tactic Notation "basic_solve_n'"    int_or_var(n) := try solve [basic_nosolve_n'    n].
Tactic Notation "basic_solve_fo_n"  int_or_var(n) := try solve [basic_nosolve_fo_n  n].
Tactic Notation "basic_solve_fo_n'" int_or_var(n) := try solve [basic_nosolve_fo_n' n].

(* `eauto` and the like default to `5` *)
Ltac basic_nosolve     := basic_nosolve_n     5.
Ltac basic_nosolve'    := basic_nosolve_n'    5.
Ltac basic_nosolve_fo  := basic_nosolve_fo_n  5.
Ltac basic_nosolve_fo' := basic_nosolve_fo_n' 5.

Ltac basic_solve     := try solve [basic_nosolve].
Ltac basic_solve'    := try solve [basic_nosolve'].
Ltac basic_solve_fo  := try solve [basic_nosolve_fo].
Ltac basic_solve_fo' := try solve [basic_nosolve_fo'].

Ltac solve_by_inv_hyp_about A :=
  multimatch goal with
    | [ H : context [?A] |- _ ] => solve [inversion H; basic_solve]
  end.


(*******************************)
(**** Hypothesis processing ****)
(*******************************)

(** Automatic Specialization **)

(* Automatically specializing context hyps that quantify type T to t (assumes t : T) *)
Ltac spec_all_type t T :=
  repeat match goal with
    | [H : forall _ : T, _ |- _ ] => specialize (H t)
  end.

(* Version that recovers the type *)
Ltac spec_all t :=
  let T := type of t in
  spec_all_type t T.

(* Automatically instantiating induction hypotheses when their premises are available in the context *)
Ltac autoprem :=
  repeat match goal with
    | [H : ?P → ?Q, p : ?P |- _] =>
      move: H; move /(_ p) => H
    end.



(** Bookkepping **)
Ltac revert_all :=
  repeat match goal with
      | [ H : _ |- _ ] => revert H
    end.

Ltac revert_all_with t :=
  repeat match goal with
      | [ H : _ |- _ ] => try t H; revert dependent H
    end.

(* Revert all except H (and other hyps it might depend on) *)
Ltac revert_except H :=
  repeat match goal with
    | [ H' : _ |- _ ] => tryif constr_eq H H' then fail else revert H'
  end.

(* TODO: use match instead to respect names *)
Ltac intro_all_with t :=
  repeat
    (let x := fresh in intro x; try (t x)).


Ltac disjunction_assumption :=
  match goal with
    | [H : ?P |- ?P]     => exact H
    | [H : ?P |- ?P ∨ _] => left; exact H
    | [       |- _  ∨ _] => right; disjunction_assumption
  end.


(* This version does NOT check if the inversion produces only one goal *)
Ltac invert_and_clear H := inversion H; clear H.

(* This one does *)
Ltac safe_invert_and_clear H := invert_and_clear H; only_one_goal.


(* Refactoring tactic: mark H as cleared without actually clearing it. This is 
   useful for temporarily fragile scripts that rely on generated names. *)
Inductive _cleared : Prop :=
  | _erase : forall P : Prop, P -> _cleared.
Ltac softclear H :=
  apply _erase in H.


(* Technical, tactic-internal: wrap an hypothesis in a dummy pair, so that it doesn't get picked-up by, say, a match goal
   This is useful to avoid processing an hypothesis multiple times (ending up in an infinite loop) or to prevent an hypothesis from
   being processed entirely, based on some criteria. *)
Definition wrap : forall P : Prop, P -> P * True := fun _ p => (p, I).
Ltac wrap_hyp H := apply wrap in H.
Ltac unwrap_all := repeat match goal with
    | [ H : _ * True  |- _      ] => destruct H as [H _]
  end.


(* FIXME: copying this here, temporarily *)
Lemma AnnCtx_uniq G : AnnCtx G -> uniq G.
Proof. by elim=> * //=; apply uniq_cons. Qed.

Ltac prove_this stmt name :=
(* let name := fresh in *)
  match stmt with
    | uniq toplevel =>
      have name: uniq toplevel by eauto
    | uniq ?G =>
      match goal with
      | [ HG : AnnCtx G |- _ ] =>
        (* let name := fresh in *)
        move: (AnnCtx_uniq HG) => name (* ; name *)
      end
    end.


(* This tactic finds "invertible" hyps (that is, the one that, once inverted, add information without generating multiple subgoals) and invert them. They are wrapped up afterwards to
   avoid inverting them again. *)
Ltac find_invertible_hyps := (* FIXME: finish + make sure it's uniform *)
  repeat (
  match goal with
    (* TODO: should we keep this hyp around? -> wrap *)
    | [ H : AnnIso _ _ (g_EqCong _ _ _) _ _ |- _ ] => invert_and_clear H
    (* FIXME: actually, we may just want to do the general case - check if this indeed working well, and if so delete previous line *)
    | [ H : AnnIso _ _ (_ _) _ _ |- _ ] => inversion H; wrap_hyp H

    (* Key step: invert typing hyps *)
    (* TODO: do we want to keep the original hyp - wrap - or clear it? *)
    | [ H : AnnTyping _ (_ _) _ _ |- _ ] => inversion H; wrap_hyp H


    | [H : _ ⊨ (_ _) : _ |- _] => safe_invert_and_clear H
    | [H : PropWff _ (Eq _ _ _ _) |- _] => safe_invert_and_clear H
    | [H : RhoCheck _ _ _ |- _] => safe_invert_and_clear H

  (* TODO: rhochecks, deq as well *)
  (* TODO *)
  end).


(* TODO: if we still apply the thm here, find another name *)
Ltac pair_coupled_hyps :=
  repeat match goal with
    | [ H1 : binds ?T _ ?G, H2 : binds ?T _ ?G |- _ ] =>
      let unG := fresh "uniq" G in
      prove_this (uniq G) unG;
      move: (binds_unique _ _ _ _ _ H1 H2 unG) => ?; wrap_hyp H2

  end;
  unwrap_all.


Ltac simp_hyp H :=
  match type of H with
    | _ ∧ _ =>
      let H1 := fresh H in
      let H2 := fresh H in
      move: H => [H1 H2];
      simp_hyp H1;
      simp_hyp H2
    | ∃ _, _ =>
      let x := fresh "x" in
      let H1 := fresh H  in
      move: H => [x H1];
      simp_hyp H1
    | _ => idtac
  end.


(* Simple forward reasoning *)
Ltac fwd :=
  repeat match goal with
    | [ H₁ : ?T₁ → ?T₂, H₂ : ?T₁ |- _] => let h := fresh H₁ H₂ in move: (H₁ H₂) => ?; wrap_hyp H₂ (* Not clear which one to wrap *)
  end.


(* Put hyps in a more exploitable shape *)
Ltac pcess_hyps :=
  find_invertible_hyps;

  repeat (
    match goal with
      | [ H : _ ∧ _       |- _ ] => destruct H

      | [ H : exists x, _  |- _ ] => destruct H

      (* For some tricks, we put hyps in this isomorphic form - pcess_hyps gets back the original hyp *)
      | [ H : _ * True  |- _      ] => destruct H as [H _]

      (* In some automation, it is hard not to generate trivial (or already obtained) facts. We make sure here to remove such useless hyps *)
      | [ H :                   ?A = ?A |- _ ] => clear H
      | [ H : forall _,         ?A = ?A |- _ ] => clear H
      | [ H : forall _ _,       ?A = ?A |- _ ] => clear H
      | [ H : forall _ _ _,     ?A = ?A |- _ ] => clear H
      | [ H : forall _ _ _ _,   ?A = ?A |- _ ] => clear H
      | [ H : forall _ _ _ _ _, ?A = ?A |- _ ] => clear H
      (* Removing redundant hyps *)
      | [ H : ?P |- _ ] => clear H; let x := fresh in assert (x : P) by solve [assumption | trivial]; clear x

      (* Basic injection code. We rely on the redundant hyps removal *)
      | [ H : ?C _                         = ?C _                         |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _                       = ?C _ _                       |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _                     = ?C _ _ _                     |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _                   = ?C _ _ _ _                   |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _                 = ?C _ _ _ _ _                 |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _ _               = ?C _ _ _ _ _ _               |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _ _ _             = ?C _ _ _ _ _ _ _             |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _ _ _ _           = ?C _ _ _ _ _ _ _ _           |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _ _ _ _ _         = ?C _ _ _ _ _ _ _ _ _         |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _ _ _ _ _ _       = ?C _ _ _ _ _ _ _ _ _ _       |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _ _ _ _ _ _ _     = ?C _ _ _ _ _ _ _ _ _ _ _     |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _ _ _ _ _ _ _ _   = ?C _ _ _ _ _ _ _ _ _ _ _ _   |- _ ] => injection H; clear H; intros; try subst
      | [ H : ?C _ _ _ _ _ _ _ _ _ _ _ _ _ = ?C _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ ] => injection H; clear H; intros; try subst


    end);

  pair_coupled_hyps.

Ltac pre :=
  repeat (intros; try split);
  (*split_hyp;*)
  unfold "~" in *.

Ltac pre' :=
  repeat (intros; try split);
  pcess_hyps;
  unfold "~" in *.


Ltac prove_eq_same_head :=
  solve [subst; reflexivity | f_equal; basic_solve].


(************************************)
(**** Handling of free variables ****)
(************************************)

Tactic Notation "pick" "fresh" := let x := fresh "x" in pick fresh x.

(** Ad-hoc version of fsetdec, hopefully faster **)
(* TODO: handle the subset-union cases (see fc_dec.v) *)
Ltac break_union :=
  repeat match goal with
  (* TODO: see if there are other common cases we could solve here *)
    | [ H : ~ ?x `in` union _ _ |- _ ] =>
        move: (notin_union_1 _ _ _ H) (notin_union_2 _ _ _ H) => ??; clear H
  end.

Ltac fsetdec_fast := solve [break_union; basic_solve_n 3].


(** Autofresh: instantiate all co-finitely quantified assumptions with the same variable **)
(* These tactics have 2 versions: the first one, without suffix, is to be used when there is
   only one variable we are interested in. Hypotheses are then *specialized* - that is, we
   loose the original universal assumption while making the specific instance. The versions
   with a '+' suffic are meant to be used when there are multiple variables involved; they
   add the relevant instances without discarding the original hypothesis. *)
Ltac autofresh_fixed_param tac x :=
    (* Trying to spot the freshness assumption and to make it as general as possible
    (in case the co-domain is an evar) *)
    try (
      match goal with
        | [H : x `notin` _ |- _] =>
          let l := gather_atoms in
          instantiate (1 := l) in H
      end);
  (* Instantiating all co-finitely quantified hyps *)
   repeat match goal with
     | [ H : ∀ x' : atom, x' `notin` ?L -> _ |- _] =>
       let xL := fresh x L in
       (have xL : x `notin` L by first [fsetdec_fast | fsetdec]);
       tac H x xL;
       simp_hyp H;
       wrap_hyp H;
       clear xL (* Clear specialized freshness assumptions *)
   end;
   unwrap_all.



 (* General version that picks up a fresh variable instead *)
 Ltac autofresh_param tac :=
   let x := fresh "x" in
   pick fresh x;
   autofresh_fixed_param tac x.



(** General purpose automation tactic tailored for this development **)

(* Placeholder tactics meant to be redifined in the corresponding files *)
Tactic Notation "tactic-not-avail" ident(name) :=
  idtac "Info: tactic" name "isn't implemented at this point in the proof.";
  idtac "Make sure to import the corresponding file if it is needed.".



(* Try to find some kind of contradiction (for the most common cases of contradiction we encounter here) *)
Ltac contra_solve := 
  try discriminate

  (* TODO: other cases *)

(*   repeat match goal with
  end *) .

(* Stand-alone version *)
Ltac autocontra :=
  pcess_hyps;
  contra_solve.


(* Doing as much forward reasoning as possible *)
Ltac autofwd :=
  pcess_hyps;
  try fwd;
  try contra_solve
  (* TODO: what else? *).



(* TODO: rely on autoreg, autoinv, etc *)
Ltac autotype :=
  pcess_hyps;

(* TODO: can use exactly once for inversions *)
(* TODO: integrate the relevant ad-hoc tactics declared in different files *)
  repeat match goal with
    | [ |- _ ∧ _ ] => split

    (* Force failure if fsetdec can't solve this goal (there shouldn't be cases where other tactics can solve it) *)
    | [ |- _ `in` _   ] => try fsetdec_fast; first [fsetdec | fail 2]
    | [ |- ¬ _ `in` _ ] => try fsetdec_fast; first [fsetdec | fail 2]


    | [ |- _ [=] _  ] => first [fsetdec | fail 2]
    | [ |- _ [<=] _ ] => first [fsetdec | fail 2]


    | [ |- ?C _                         = ?C _                         ] => prove_eq_same_head
    | [ |- ?C _ _                       = ?C _ _                       ] => prove_eq_same_head
    | [ |- ?C _ _ _                     = ?C _ _ _                     ] => prove_eq_same_head
    | [ |- ?C _ _ _ _                   = ?C _ _ _ _                   ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _                 = ?C _ _ _ _ _                 ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _ _               = ?C _ _ _ _ _ _               ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _ _ _             = ?C _ _ _ _ _ _ _             ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _ _ _ _           = ?C _ _ _ _ _ _ _ _           ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _ _ _ _ _         = ?C _ _ _ _ _ _ _ _ _         ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _ _ _ _ _ _       = ?C _ _ _ _ _ _ _ _ _ _       ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _ _ _ _ _ _ _     = ?C _ _ _ _ _ _ _ _ _ _ _     ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _ _ _ _ _ _ _ _   = ?C _ _ _ _ _ _ _ _ _ _ _ _   ] => prove_eq_same_head
    | [ |- ?C _ _ _ _ _ _ _ _ _ _ _ _ _ = ?C _ _ _ _ _ _ _ _ _ _ _ _ _ ] => prove_eq_same_head

    | _ => try done; basic_solve; fail 0


    | [ |- ex _ ] => eexists


    (* FIXME: need to backtrack if that doesn't work *)
    (* FIXME: have a "pre" or so *)
    | [ |- AnnTyping _   (_ _) _ _  ] => econstructor; pcess_hyps
    | [ |- AnnDefEq  _ _ (_ _) _ _ _ ] => econstructor; pcess_hyps
    | [ |- AnnIso    _ _ (_ _) _ _ ] => econstructor; pcess_hyps
  end.



(** Bulldozing away these pesky free variables conditions **)
(* TODO: autotype should call autofv when needed *)

(* TODO:
  - not complete, many cases are not covered (co vars in particular)
  - right now, the following mostly implements proofs of non-inclusion. Implement inclusions
*)

(* Guard predicate: Does T 'talk about' variables? *)
Ltac guard_about_vars T :=
  match T with
    | _ ∉ _ => idtac
  end.

Ltac fresh_fireworks := (* ... a firework of freshness conditions *)
  repeat (fwd (* FIXME: should be *some* fwd reasoning, but not pcess_hyps (no unwrap) *);
    match goal with
      | [ H : _ ∉ (_ ∪ _) |- _ ] =>
          let h := fresh H in
          move: H (notin_union_1 _ _ _ H) (notin_union_2 _ _ _ H) => /= _ H h
      | [ H : _ ∉ singleton _ |- _ ] =>
          idtac "TODO: inv singleton";
          wrap_hyp H
      | [ H : _ ∉ fv_tm_tm_tm (open_tm_wrt_tm _ _) |- _ ] =>
          let h := fresh H in
          move: (subset_notin H (fv_tm_tm_tm_open_tm_wrt_tm_lower _ _)) => h;
          wrap_hyp H
      | [ H : _ ∉ fv_tm_tm_tm (open_tm_wrt_co _ _) |- _ ] =>
          let h := fresh H in
          move: (subset_notin H (fv_tm_tm_tm_open_tm_wrt_co_lower _ _)) => h;
          wrap_hyp H
      (* TODO: other cases (fv_co_co_co (open_co_wrt_co _ _)), etc *)
    end);
  (* unwrap_all -> Performed by autofv_solve, to avoid processing the same hyps several times *)
  idtac.

Ltac autofv_solve :=
  unwrap_all;
  repeat match goal with
    (* TODO (long-term): The following should be generated by lngen *)
    | [ |- _ ∉ fv_tm_tm_tm (open_tm_wrt_tm _ _) ] => solve [rewrite fv_tm_tm_tm_open_tm_wrt_tm_upper; cbn; autofv_solve | fail ]
    | [ |- _ ∉ fv_tm_tm_tm (open_tm_wrt_co _ _) ] => solve [rewrite fv_tm_tm_tm_open_tm_wrt_co_upper; cbn; autofv_solve | fail ]
    | [ |- _ ∉ fv_co_co_co (open_co_wrt_co _ _) ] => solve [rewrite fv_co_co_co_open_co_wrt_co_upper; cbn; autofv_solve | fail ]
    | [ |- _ ∉ fv_co_co_co (open_co_wrt_tm _ _) ] => solve [rewrite fv_co_co_co_open_co_wrt_tm_upper; cbn; autofv_solve | fail ]
    | [ |- _ ∉ fv_tm_tm_co (open_co_wrt_tm _ _) ] => solve [rewrite fv_tm_tm_co_open_co_wrt_tm_upper; cbn; autofv_solve | fail ]
    | [ |- _ ∉ fv_tm_tm_co (open_co_wrt_co _ _) ] => solve [rewrite fv_tm_tm_co_open_co_wrt_co_upper; cbn; autofv_solve | fail ]
    | [ |- _ ∉ fv_co_co_tm (open_tm_wrt_co _ _) ] => solve [rewrite fv_co_co_tm_open_tm_wrt_co_upper; cbn; autofv_solve | fail ]
    | [ |- _ ∉ fv_co_co_tm (open_tm_wrt_tm _ _) ] => solve [rewrite fv_co_co_tm_open_tm_wrt_tm_upper; cbn; autofv_solve | fail ]

    | [ |- _ ∉ (_ ∪ _) ] => eapply not_in_union

  end;
  solve [fsetdec_fast | fsetdec | eauto].


Ltac autofv_fwd :=
  fresh_fireworks;
  repeat (match goal with
    | [ H : ?T₁ → ?T₂ |- _ ] =>
      guard_about_vars T₁;
      let t₁ := fresh in
      (have t₁ : T₁ by autofv_solve);
      move: {H} (H t₁) => H
  end; fresh_fireworks).

Ltac autofv :=
  autofv_fwd;
  autofv_solve.


End TacticsInternals.



(**** High-level tactics (made for users) ****)
(* TODO: when tactics are fully implemented, we might want to put this in a different file *)

(* Add pointers to canonical examples *)

(* General purpose solver. Does a bunch of domain-specific reasoning *)
Ltac basic_solve := TacticsInternals.basic_solve.
Ltac split_hyp := TacticsInternals.split_hyp.
Ltac autotype   := TacticsInternals.autotype.
Ltac ok         := autotype.

(* Does as much forward reasoning as possible (includes deriving contradictions) *)
Ltac autofwd    := TacticsInternals.autofwd.
Ltac introfwd   := intros; autofwd.

(* TODO Tries to solve free variable obligations *)
Ltac autofv     := TacticsInternals.autofv.

(* Tries to find some kind of contradiction (for the most common cases of contradiction we encounter here) *)
Ltac autocontra := TacticsInternals.autocontra.

(* Automatically pick fresh variables and solve freshness conditions *)
Tactic Notation "autofresh"  "with" hyp(x) := TacticsInternals.autofresh_fixed_param TacticsInternals.spec2 x.
Tactic Notation "autofresh+" "with" hyp(x) := TacticsInternals.autofresh_fixed_param TacticsInternals.inst2 x.
Tactic Notation "autofresh" "for" "all" := fail "TODO". (* /!\ issues with unwrap_all *)
Tactic Notation "autofresh"  := TacticsInternals.autofresh_param TacticsInternals.spec2.
Tactic Notation "autofresh+" := TacticsInternals.autofresh_param TacticsInternals.inst2.

Ltac depind x   := dependent induction x.


(* Misc *)
Ltac clearall := TacticsInternals.clearall.
Tactic Notation "clear all" := TacticsInternals.clearall.
Tactic Notation (at level 0) "revert" "all" "except" ident(H) := TacticsInternals.revert_except H.

Tactic Notation "exactly" integer(n) "goal" := TacticsInternals.check_num_goals_eq n.
Tactic Notation "exactly" integer(n) "goals" := TacticsInternals.check_num_goals_eq n.

Ltac invs := TacticsInternals.invs.
Ltac softclear := TacticsInternals.softclear.

(* FIXME: rely on internals *)
Tactic Notation "basic_nosolve_n" int_or_var(n) := intuition (subst; eauto n).
Tactic Notation "basic_solve_n" int_or_var(n) := try solve [basic_nosolve_n n].

