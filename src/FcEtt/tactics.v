Require Import FcEtt.imports.

Require Import FcEtt.ett_inf.

Require Import FcEtt.fset_facts.

Import AtomSetFacts AtomSetProperties.

Require Import FcEtt.notations.

Require Export FcEtt.tactics_safe.
Require Export FcEtt.tactics_ecomp.

Require Import Coq.Strings.String.

(**** Tactics for the project ****)


(* Hints & databases *)

(* Rewrite db with standard facts, like general stuff we use all the time *)
Hint Rewrite map_app app_assoc : std.

(* `one` tends to get in the way *)
Definition unfold_one : `(forall (t : T), one t = t :: []) := ltac:(done).
Hint Rewrite unfold_one : std.


(* Module for the types that some tactics rely on. We don't want to export these types - only their
   notations, defined below. *)
Module TacticsTypes.

  (* Dynamic type *)
  Polymorphic (* Cumulative *) Inductive Dyn : Type := dyn : forall {T : Type}, T -> Dyn.

  (* Currently unused *)
  Inductive Display {T : Type} : T → Prop := display : ∀ (t : T), Display t.

  (* Hiding/unhiding the type of a hyp *)
  Polymorphic Definition _hide         {T : Type}              (t : T) : T                  := t.
  Polymorphic Definition _hide_with    {T : Type} (s : string) (t : T) : T                  := t.
  Polymorphic Definition _eq_hide      {T : Type}              (t : T) : t = _hide t        := eq_refl.
  Polymorphic Definition _eq_hide_with {T : Type} (s : string) (t : T) : t = _hide_with s t := eq_refl.

End TacticsTypes.

(* Exported notations *)
Notation "![ ]!" := nil (format "![ ]!") : list_scope.
Notation "![ x ]!" := (cons (TacticsTypes.dyn x) nil) : list_scope.
Notation "![ x ; y ; .. ; z ]!" := (cons (TacticsTypes.dyn x) (cons (TacticsTypes.dyn y) .. (cons (TacticsTypes.dyn z) nil) ..)) : list_scope.

Global Notation "'_hidden_'"       := (TacticsTypes._hide _)        (at level 50, only printing).
Global Notation "'_hidden_' ( s )" := (TacticsTypes._hide_with s _) (at level 50, only printing).



Module TacticsInternals.
(*******************************)
(**** Basic Building Blocks ****)
(*******************************)

Import TacticsTypes.

Ltac nl := idtac " ".

Local Tactic Notation "ret" tactic(tac) := let answer := tac in exact answer.

(* Shorthands for instantiation/specialization *)
Ltac spec2 H x xL := specialize (H x xL).
Ltac inst2 H x xL := let h := fresh H x in move: (H x xL) => h.

Ltac especialize H :=
  repeat match type of H with
    | forall (x : ?t), _ =>
      let e := fresh "e" in
      evar (e : t);
      move: H;
      move/(_ e) => H;
      subst e
  end.

(**** More powerful apply tactic ****)
(* Aux *)
Ltac align_type_hyp_vs t t_H H :=
  first [
    unify t t_H (* ; idtac "Done - heads are unifiable:"; idtac t; idtac t_H *)
  |
    match t with
      | ?t1 ?t2 =>
        match t_H with
          | ?t_H1 ?t_H2 =>
            first [
              (* Arguments' types match, we good *)
              unify t2 t_H2; align_type_hyp_vs t1 t_H1 H
            |
              have: (t2 = t_H2);
                [ (* eq aligning the arguments' types, left to the user *) |
                  move=> ->; align_type_hyp_vs t1 t_H1 H  ]
            ]
          end
      | _ =>
        (* Can't decompose t further. What about t_H? *)
        lazymatch t_H with
          | ?t_H1 ?t_H2 =>
            fail "Can't align types: not the same number of arguments"
          | _ =>
            idtac "Done, but heads are not unifiable. This might mean we're applying the wrong hyp/term - unless this is expected";
            idtac t; idtac t_H;
            have->: (t = t_H)
        end
    end].

(* "Apply modulo equalities": applies `hyp_or_tm` to the goal and generates equalities for
    the arguments that don't unify *)
Ltac apply_eq hyp_or_tm :=
  first [
    eapply hyp_or_tm
  |
    (* hyp_or_tm can be a constr (which includes a mere hyp ident) or a uconstr (eset accepts both) *)
    let f := fresh "f" in
    eset (f := hyp_or_tm);
    clearbody f; (* To match apply's behavior *)
    especialize f; (* Instantiate f with evars as needed *)
    let g := match goal with |- ?G => G end in
    let t := type of f in
    align_type_hyp_vs g t f;
    last first;
    only 1: apply f;
    clear f
   ].

(**** Info tactics ****)
(* This tactic is meant to help find why 2 terms are not unifiable, by displaying
   additional information. At the moment, it only decomposes applications. Foralls
   can be handled using especialize. *)
Ltac unify_info' disp1 disp2 t1 t2 :=
  tryif unify t1 t2 then idtac "Success," t1 "and" t2 "are unifiable"
  else lazymatch t1 with
    | ?t11 ?t12 =>
      lazymatch t2 with
        | ?t21 ?t22 =>
          tryif unify t12 t22 then
            idtac "Unifiable arguments:" t12 t22;
            unify_info' disp1 disp2 t11 t21
          else
            (* Splitting this message so that the terms are vertically aligned *)
            idtac "__Failure: can't unify arguments__";
            idtac disp1 t12;
            idtac disp2 t22;
            nl;
            idtac "Corresponding functions:";
            idtac disp1 t11;
            idtac disp2 t21;
            nl; nl;
            idtac "Trying recursively:";
            unify_info' disp1 disp2 t12 t22;
            fail "Unification failure"
        | _ => fail "Can't decompose" disp2 t2 "further"
      end
    | _ => fail "Can't decompose" disp1 t1 "further"
  end.


(* Tactic that succeeds only if `t` fails to unify with every element of `l` *)
Ltac avoid_unify_list t l :=
  lazymatch l with
    | dyn ?t' :: ?tl =>
      tryif assert_fails unify t t'
      then avoid_unify_list t tl
      else fail "Unifiable with an element of the list"
    | [] => idtac
    | _ => fail 99 "avoid_unify_list: incorrect argument given"
  end.


Ltac hide H       := match type of H with | _hide ?T => rewrite <- (_eq_hide T) in H | _hide_with ?s ?T => rewrite <- (_eq_hide_with s T) in H | ?T => rewrite -> (_eq_hide T) in H end.
Ltac hidewith s H := match type of H with | _hide ?T => rewrite <- (_eq_hide T) in H | _hide_with ?s ?T => rewrite <- (_eq_hide_with s T) in H | ?T => rewrite -> (_eq_hide_with s T) in H end.
Ltac unhide H     := match type of H with | _hide ?T => rewrite <- (_eq_hide T) in H | _hide_with ?s ?T => rewrite <- (_eq_hide_with s T) in H | _ => fail "Not hidden" end.
Ltac unhide_all   := repeat match goal with | H : _hide _ |- _ => unhide H end; repeat match goal with | H : _hide_with _ _ |- _ => unhide H end.


Ltac unwrap_dyn d :=
  match d with
    | dyn ?v => v
  end.

(* Checks that `t` is a multi-application headed by `hd`; `hd` doesn't have to be a mere constructor,
   it can also be applied to some arguments *)
Ltac has_head t hd :=
  match t with
    | hd => idtac
    | ?hd' _ => has_head hd' hd
  end.

(* Variant of `has_head_uconstr` that allows t to be headed by lambdas *)
(* This version succeeds by returning `fun x1 ... xn => tt`, and fails otherwise *)
Ltac has_head_quant_ret t hd :=
  match t with
    | hd => tt
    (* We're technically allowing interleavings of lambdas and applications. Not sure that's a problem..? *)
    | fun (x : ?t') => @?tl x => constr:(fun (x : t') => ltac:(ret has_head_quant_ret ltac:(eval hnf in (tl x)) hd))
    | ?hd' _ => has_head_quant_ret hd' hd
  end.

(* More general version: this time, `hd` is a uconstr, not a constr (hence the hacky workaround with refine).
   This allows to specify `hd` as a pattern, even a partial one.
   For instance, these (simplified) examples should succeed:
     has_head_uconstr (Vector 3 nat) (Vector _ nat)
     has_head_uconstr (Vector 3 nat) (Vector _)
*)
Ltac has_head_uconstr t hd :=
  first [
    let T := fresh in
    (* There might be a way to use a simpler type for unification but it didn't seem to work just as well (e.g. with Display above) *)
    have _: exists T, T = t by refine (@ex_intro _ _ hd (eq_refl _))
  |
    match t with
      | ?t' _ => has_head_uconstr t' hd
    end
  ].

(* Auxiliary tactics for `has_head_uconstr_quant` *)
(* Generates the type    forall x1 ... xn, exists T, T = t'
   with t = fun x1 ... xn => t'
   (thus t' depends on x1, ..., xn) *)
Ltac unfold_test_eq T t :=
  match t with
    | fun (x : ?t) => @?tl x =>
      constr:(forall (x : t), ltac:(ret unfold_test_eq T ltac:(eval hnf in (tl x))))
    | _ =>
      constr:(exists T, T = t)
  end.

(* "Removes" the last argument of an eta-expanded function.
    Note that the binder corresponding to that argument is _not_ removed.
   Eg,   fun G a A => Typing G a A   is turned into   fun G a _ => Typing G a  *)
Ltac remove_arg a :=
  match a with
    | fun (x : ?t) => @?b x =>
      constr:(fun (x : t) => ltac:(ret remove_arg ltac:(eval hnf in (b x))))
    | ?t' _ => t'
  end.

(* Variant of `has_head_uconstr` that allows t to be headed by lambdas *)
Ltac has_head_uconstr_quant t hd :=
  first [
    let T := fresh in
    (* There might be a way to use a simpler type for unification but it didn't seem to work just as well (e.g. with Display above) *)
    have _: ltac:(ret unfold_test_eq T t) by intros; refine (@ex_intro _ _ hd (eq_refl _))
  |
    has_head_uconstr_quant ltac:(remove_arg t) hd
  ].

(* Takes a term `t` of shape `fun (x1 : T1) ... (xn : Tn) => tt` and strips its arguments' types `T1`, ... `Tn` (replaced by unit)
   This tactic returns the result directly or fails if `t` isn't of the right shape *)
Ltac strip_arg_type t :=
  match t with
    | tt => tt
    | fun (x : ?t') => @?tl x =>
      (* First erase arguments recursively (need to start from the innermost arguments, to preserve remaining dependencies at all stages) *)
      let r := constr:(fun (x : t') => ltac:(ret strip_arg_type ltac:(eval hnf in (tl x)))) in
      (* Then replace the function - that we *now* know doesn't depend on x anymore - with an equivalent function having argument unit.
        (that way, we're removing the dependencies of x's type (t') on previous arguments, in turn allowing them to be erased) *)
      match r with fun (x : _) => ?tl' => constr:(fun (x : unit) => tl') end
  end.

(* This tactic spots the nth argument of type `pi` whose type's head is hd.
   Its result is in skeletal shape, i.e. fun x1 ... xk => tt (meaning the argument is the (k+1)th argument in pi)
   In particular, doing so allows bypassing some of the binding-manipulation shortcomings of ltac *)
Ltac spot_arg_with_head pi hd nth :=
  match pi with
    | forall (x : ?t), @?tl x =>
      (* Check that the argument matches (we don't use `discard`, it's just a way to test whether `has_head_quant_ret` succeeds) *)
      let discard := has_head_quant_ret t hd in
      (* Ok, the type of the argument matches; now, do we want this one or a later one? *)
      match nth with
        | O => tt
        | S ?pred => constr:(fun (x : t) => ltac:(ret spot_arg_with_head ltac:(eval hnf in (tl x)) hd pred)) (* Recursive call with tl & pred (both args decreasing) *)
        | _ => fail 2 (* Not needed for correctness, only to optimize this failure case *)
      end
    | forall (x : ?t), @?tl x =>
      (* Previous branch didn't match, meaning the argument's type didn't match. Check the next. *)
      constr:(fun (x : t) => ltac:(ret spot_arg_with_head ltac:(eval hnf in (tl x)) hd nth))           (* Recursive call with tl & nth (pi decreasing, nth unchanged) *)
  end.


(* Find an hypothesis which type is headed by constructor `cs`, and
   apply `tac` to it. Parametrized by `head_check` for efficiency vs
   generality trade-off *)
Ltac find_hyp_and_perform head_check cs tac :=
    match goal with
      H : ?t |- _ => head_check t cs; (* idtac "Matching hyp:" H; *) tac H end.

(* Optimization (of the previous one): first tries to use the typed version if possible, otherwise falls back to the slow, general one *)
Ltac find_hyp_and_perform_optim cs tac :=
  tryif
    let cs' := type_term cs in
    (* idtac "Switching to fast mode" *)
    idtac (* Silent *)
  then
    let cs' := type_term cs in
    find_hyp_and_perform has_head cs' tac
  else
    find_hyp_and_perform has_head_uconstr cs tac.



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

Ltac subst_forall :=
  repeat find_eq_rew_clear.


Ltac check_num_goals_eq g := let n:= numgoals in guard n=g.


Ltac inv  H := inversion H. (* Alias - supports partial application *)
Ltac invs H := inversion H; subst. (* Inversion and substitution (think "InvS") *)
Ltac applyin f H := apply f in H.

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

(* Specialize hypothesis H, solving obligations with solver *)
Ltac spec_hyp H solver :=
  lazymatch type of H with
    | forall x : ?T, _ =>
      move: H; move/(_ ltac:(solver)) => H; spec_hyp H solver
    | _ => idtac
  end.


(* Automatically instantiating induction hypotheses when their premises are available in the context. *)
Ltac autoprem solver :=
  repeat match goal with
    | H : forall x : ?P, _, p : ?P |- _ =>
      move: H; move /(_ p) => H
    | H : forall x : ?P, _ |- _ =>
      move: H; move/(_ ltac:(eassumption || auto 5)) => H
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
Ltac find_invertible_hyps :=
  repeat (
  match goal with
    | [ H : AnnIso _ _ (g_EqCong _ _ _) _ _ |- _ ] => invert_and_clear H
 
    | [ H : AnnIso _ _ (_ _) _ _ |- _ ] => inversion H; wrap_hyp H

    (* Key step: invert typing hyps *)
    | [ H : AnnTyping _ (_ _) _ _ |- _ ] => inversion H; wrap_hyp H


    | [H : _ ⊨ (_ _) : _ |- _] => safe_invert_and_clear H
    | [H : PropWff _ (Eq _ _ _ _) |- _] => safe_invert_and_clear H
    | [H : RhoCheck _ _ _ |- _] => safe_invert_and_clear H

  end).


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
Ltac break_union :=
  repeat match goal with
    | [ H : ¬ ?x `in` union _ _ |- _ ] =>
        move: (notin_union_1 _ _ _ H) (notin_union_2 _ _ _ H) => ??; clear H
  end.

Ltac fsetdec_fast := solve [break_union; basic_solve_n 3].


(** Autofresh: instantiate all co-finitely quantified assumptions with the same variable **)
(* These tactics have 2 versions: the first one, without suffix, is to be used when there is
   only one variable we are interested in. Hypotheses are then *specialized* - that is, we
   loose the original universal assumption while making the specific instance. The versions
   with a '+' suffic are meant to be used when there are multiple variables involved; they
   add the relevant instances without discarding the original hypothesis. *)
Ltac autofresh_fixed_param' tac x :=
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

Ltac hide_fresh_hyps x hide :=
  tryif hide then
    repeat match goal with
      H : x ∉ _ |- _ => hidewith "freshness" H
    end
  else idtac.

Ltac autofresh_fixed_param tac x hidefresh :=
  autofresh_fixed_param' tac x;
  hide_fresh_hyps x hidefresh.

(* General version that picks up a fresh variable instead *)
Ltac autofresh_param tac hidefresh :=
  let x := fresh "x" in
  pick fresh x;
  autofresh_fixed_param' tac x;
  hide_fresh_hyps x hidefresh.

(* Yet another version, that tries to find a suitable variable in the context *)

Ltac autofresh_find_param tac :=
  match goal with
    x : atom, _ : ?x `notin` _ |- _ => autofresh_fixed_param' tac x
  end.



(** General purpose automation tactic tailored for this development **)

(* Placeholder tactics meant to be redifined in the corresponding files *)
Tactic Notation "tactic-not-avail" ident(name) :=
  idtac "Info: tactic" name "isn't implemented at this point in the proof.";
  idtac "Make sure to import the corresponding file if it is needed.".



(* Try to find some kind of contradiction (for the most common cases of contradiction we encounter here) *)
Ltac contra_solve := 
  try discriminate


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
  try contra_solve.



Ltac autotype :=
  pcess_hyps;

  repeat match goal with
    | [ |- _ ∧ _ ] => split

    (* Force failure if fsetdec can't solve this goal (there shouldn't be cases where other tactics can solve it) *)
    | [ |- _ `in` _   ] => unhide_all; try fsetdec_fast; first [fsetdec | fail 2]
    | [ |- ¬ _ `in` _ ] => unhide_all; try fsetdec_fast; first [fsetdec | fail 2]


    | [ |- _ [=] _  ] => first [unhide_all; fsetdec | fail 2]
    | [ |- _ [<=] _ ] => first [unhide_all; fsetdec | fail 2]


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


    | [ |- AnnTyping _   (_ _) _ _  ] => econstructor; pcess_hyps
    | [ |- AnnDefEq  _ _ (_ _) _ _ _ ] => econstructor; pcess_hyps
    | [ |- AnnIso    _ _ (_ _) _ _ ] => econstructor; pcess_hyps
  end.



(** Bulldozing away these pesky free variables conditions **)

(* Guard predicate: Does T 'talk about' variables? *)
Ltac guard_about_vars T :=
  match T with
    | _ ∈ _ => idtac
    | _ ∉ _ => idtac
  end.

Ltac fresh_fireworks := (* ... a firework of freshness conditions *)
  repeat (fwd;
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
    end);
  (* unwrap_all -> Performed by autofv_solve, to avoid processing the same hyps several times *)
  idtac.

Ltac autofv_solve :=
  unwrap_all;
  repeat match goal with
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
    | H : ?T₁ → ?T₂ |- _ =>
      guard_about_vars T₁;
      let t₁ := fresh in
      (have t₁ : T₁ by autofv_solve);
      move: {H} (H t₁) => H;
      fresh_fireworks
    | H : _ ∈ empty |- _ =>
      apply notin_empty_1 in H;
      contradiction
    | H : ?y ∈ singleton ?x |- _ =>
      assert (x = y) by auto;
      subst;
      clear H
    | H : binds _ _ _ |- _ =>
      apply binds_In in H
  end).

Ltac autofv :=
  autofwd;
  autofv_fwd;
  autofv_solve.


End TacticsInternals.



(**** High-level tactics (made for users) ****)

(* Add pointers to canonical examples *)


(** Solvers **)

Ltac basic_solve  := TacticsInternals.basic_solve.
Ltac split_hyp    := TacticsInternals.split_hyp.

(* General purpose solver. Does a bunch of domain-specific reasoning *)
Ltac autotype     := TacticsInternals.autotype.
Ltac ok           := autotype.

(* Does as much forward reasoning as possible (includes deriving contradictions) *)
Ltac autofwd      := TacticsInternals.autofwd.
Ltac introfwd     := intros; autofwd.
Ltac autoprem     := TacticsInternals.autoprem.
Ltac autospec H   := TacticsInternals.spec_hyp H ltac:(solve [eassumption | eauto 2]).
Ltac autospec' H sol := TacticsInternals.spec_hyp H sol.

(* Heterogeneous apply - applies hyp even if types don't unify (generating equality obligations as needed) *)
(* Note: open to more canonical naming - suggestions welcome *)
Tactic Notation "happly" uconstr(arg) := TacticsInternals.apply_eq arg.
Ltac ha                               := TacticsInternals.apply_eq. (* Shorter version, can be passed as argument. Wrap arg in uconstr:() if needed *)


Ltac autofv       := TacticsInternals.autofv.
Ltac fsetdec_fast := TacticsInternals.fsetdec_fast.

(* Tries to find some kind of contradiction (for the most common cases of contradiction we encounter here) *)
Ltac autocontra := TacticsInternals.autocontra.

(* Automatically pick fresh variables and solve freshness conditions *)
Tactic Notation "autofresh"  "with" hyp(x) := TacticsInternals.autofresh_fixed_param TacticsInternals.spec2 x idtac.
Tactic Notation "autofresh'"  "with" hyp(x) := TacticsInternals.autofresh_fixed_param TacticsInternals.spec2 x fail.
Tactic Notation "autofresh+" "with" hyp(x) := TacticsInternals.autofresh_fixed_param TacticsInternals.inst2 x idtac.
Tactic Notation "autofresh'+" "with" hyp(x) := TacticsInternals.autofresh_fixed_param TacticsInternals.inst2 x idtac.
Tactic Notation "autofresh"  "with" "existing" := TacticsInternals.autofresh_find_param TacticsInternals.spec2.
Tactic Notation "autofresh+" "with" "existing" := TacticsInternals.autofresh_find_param TacticsInternals.inst2.
Tactic Notation "autofresh" "for" "all" := fail "TODO". (* /!\ issues with unwrap_all *)
Tactic Notation "autofresh"  := TacticsInternals.autofresh_param TacticsInternals.spec2 idtac.
Tactic Notation "autofresh'"  := TacticsInternals.autofresh_param TacticsInternals.spec2 fail.
Tactic Notation "autofresh+" := TacticsInternals.autofresh_param TacticsInternals.inst2 idtac.
Tactic Notation "autofresh'+" := TacticsInternals.autofresh_param TacticsInternals.inst2 fail.



(** Nameless style - finding hypotheses and processing them **)

(* Find an hypothesis which type is headed by constructor cs, and
   apply tac to it *)
(* General version, that accepts a pattern (uconstr) (hence also accepts `Typing _ a`). Will switch to a fast matching if possible *)
Tactic Notation "with" uconstr(hd) "do" tactic(tac)       := TacticsInternals.find_hyp_and_perform_optim hd tac.
Tactic Notation "with" uconstr(hd) "do" tactic(tac) "end" := TacticsInternals.find_hyp_and_perform_optim hd tac.
 Tactic Notation "with" uconstr(hd) "excl" constr(excl) "do" tactic(tac) :=
  TacticsInternals.find_hyp_and_perform_optim hd ltac:(fun h => TacticsInternals.avoid_unify_list h excl; tac h).

(* Specialized version to find and rename hypothesis *)
Tactic Notation "get" uconstr(hd) "as" ident(name) := TacticsInternals.find_hyp_and_perform_optim hd ltac:(fun h => rename h into name).
Tactic Notation "get" uconstr(hd) "excl" constr(excl) "as" ident(name) :=
  TacticsInternals.find_hyp_and_perform_optim hd ltac:(fun h => TacticsInternals.avoid_unify_list h excl; rename h into name).

(* For convenience, here are inlined version of the "excl" forms with just a few arguments.*)
Tactic Notation "with" uconstr(hd) "excl" ident(e1) "do" tactic(tac) :=
  TacticsInternals.find_hyp_and_perform_optim hd ltac:(fun h => TacticsInternals.avoid_unify_list h (![e1]!); tac h).
Tactic Notation "with" uconstr(hd) "excl" ident(e1) "," ident(e2) "do" tactic(tac) :=
  TacticsInternals.find_hyp_and_perform_optim hd ltac:(fun h => TacticsInternals.avoid_unify_list h (![e1; e2]!); tac h).
Tactic Notation "with" uconstr(hd) "excl" ident(e1) "," ident(e2) "," ident(e3) "do" tactic(tac) :=
  TacticsInternals.find_hyp_and_perform_optim hd ltac:(fun h => TacticsInternals.avoid_unify_list h (![e1; e2; e3]!); tac h).

Tactic Notation "get" uconstr(hd) "excl" ident(e1) "as" ident(name) :=
  TacticsInternals.find_hyp_and_perform_optim hd ltac:(fun h => TacticsInternals.avoid_unify_list h ![e1]!; rename h into name).
Tactic Notation "get" uconstr(hd) "excl" ident(e1) "," ident(e2) "as" ident(name) :=
  TacticsInternals.find_hyp_and_perform_optim hd ltac:(fun h => TacticsInternals.avoid_unify_list h ![e1; e2]!; rename h into name).
Tactic Notation "get" uconstr(hd) "excl" ident(e1) "," ident(e2) "," ident(e3) "as" ident(name) :=
  TacticsInternals.find_hyp_and_perform_optim hd ltac:(fun h => TacticsInternals.avoid_unify_list h ![e1; e2; e3]!; rename h into name).


(** Misc **)

Ltac clearall := TacticsInternals.clearall.
Tactic Notation "clear all" := TacticsInternals.clearall.
Tactic Notation (at level 0) "revert" "all" "except" ident(H) := TacticsInternals.revert_except H.

Tactic Notation "exactly" integer(n) "goal" := TacticsInternals.check_num_goals_eq n.
Tactic Notation "exactly" integer(n) "goals" := TacticsInternals.check_num_goals_eq n.

(* Shorthands, that can be partially applied (for those which take arguments) *)
Ltac cse      := fun h => case: h.
Ltac dstr     := fun h => destruct h.
Ltac dstrct   := dstr.
Ltac ddstr    := fun h => dependent destruction h.
Ltac inv      := TacticsInternals.inv.
Ltac invs     := TacticsInternals.invs. (* Inversion (of a hyp) and substitution *)
Ltac applyin  := TacticsInternals.applyin.
Ltac depind x := dependent induction x.
Ltac exa    x := exact x.
Ltac ea       := eassumption.

Ltac get_goal := match goal with |- ?g => constr:(g) end.

(* Hiding/unhiding the type of a hyp *)
Ltac hide      := TacticsInternals.hide.
Ltac hidewith  := TacticsInternals.hidewith.
Ltac unhide    := TacticsInternals.unhide.

Ltac uha       := TacticsInternals.unhide_all.
Tactic Notation "unhide" "all" := uha.
Ltac softclear := TacticsInternals.softclear. (* This tactic goes further, and prevents the hyp from being used again *)

Ltac especialize := TacticsInternals.especialize.

Ltac print := fun h => idtac h.


Tactic Notation "basic_nosolve_n" int_or_var(n) := intuition (subst; eauto n).
Tactic Notation "basic_solve_n" int_or_var(n) := try solve [basic_nosolve_n n].

(* To use in particular with ltac:() - indeed, recall that with this construction, one needs to
   provide a tactic that _solves a goal_, and *not* one that _returns a term_. This turns an
   instance of the latter into one of the former. *)
Tactic Notation "ret" tactic(tac) := let answer := tac in exact answer.


(* Finding out why 2 terms are not unifiable *)
(* Selectors: hyp, ehyp (especializes the hyp first), top (top assumption, à la ssr), etop, term, goal *)
Local Tactic Notation "debugunif_dispatch" preident(disp1) preident(disp2) constr(t1) constr(t2) := TacticsInternals.unify_info' disp1 disp2 t1 t2.
Tactic Notation "debug" "unify" "hyp"  ident(H1)  "vs" "hyp"  ident(H2)  := debugunif_dispatch hyp1 hyp2 ltac:(ret type of H1) ltac:(ret type of H2).
Tactic Notation "debug" "unify" "hyp"  ident(H1)  "vs" "goal"            := let g := get_goal in debugunif_dispatch hyp1 goal ltac:(ret type of H1) g.
Tactic Notation "debug" "unify" "hyp"  ident(H1)  "vs" "term" constr(t2) := debugunif_dispatch hyp trm ltac:(ret type of H1) t2.
Tactic Notation "debug" "unify" "ehyp" ident(H1)  "vs" "goal"            := especialize H1; let g := get_goal in debugunif_dispatch hyp1 goal ltac:(ret type of H1) g.
Tactic Notation "debug" "unify" "top"             "vs" "goal"            := let top := fresh "top" in move=> top; let g := get_goal in debugunif_dispatch top_ goal ltac:(ret type of top) g.
Tactic Notation "debug" "unify" "etop"            "vs" "goal"            := let top := fresh "top" in move=> top; especialize top; let g := get_goal in debugunif_dispatch etop goal ltac:(ret type of top) g.
Tactic Notation "debug" "unify" "term" constr(t1) "vs" "term" constr(t2) := debugunif_dispatch tm1 tm2 t1 t2.
Tactic Notation "debug" "unify" "term" constr(t1) "vs" "goal"            := let g := get_goal in debugunif_dispatch term goal t1 g.

