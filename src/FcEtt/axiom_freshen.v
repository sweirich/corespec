
Require Import FcEtt.imports.
Require Import FcEtt.tactics.
Require Import FcEtt.utils.

Require Import FcEtt.ett_ott.

Require Import FcEtt.ett_inf.
Require Import FcEtt.ett_ind.


Require Import FcEtt.ext_wf.
Require Export FcEtt.ext_invert.
Require Export FcEtt.ext_weak.
Require Export FcEtt.ext_subst.
Require Import FcEtt.ett_roleing.

Require Export FcEtt.ext_red_one.
Require Import FcEtt.ett_match.
Require Import FcEtt.ett_rename.

(** Some shortcuts **)

Lemma tm_subst_tm_tm_same_diff : forall x y,
       tm_subst_tm_tm (a_Var_f y) x (a_Var_f x) = a_Var_f y.
Proof. intros. simpl. destruct (x == x). auto. contradiction.
Qed.

Lemma tm_subst_tm_tm_app_same_diff : forall x y p nu,
      tm_subst_tm_tm (a_Var_f y) x (a_App p nu (a_Var_f x)) =
      a_App (tm_subst_tm_tm (a_Var_f y) x p) nu (a_Var_f y).
Proof. intros. simpl. f_equal. destruct (x == x). auto. contradiction.
Qed.

Lemma tm_subst_tm_tm_diff : forall x y z, z <> x ->
       tm_subst_tm_tm (a_Var_f y) x (a_Var_f z) = a_Var_f z.
Proof. intros. simpl. destruct (z == x). contradiction. auto.
Qed.

Lemma tm_subst_tm_tm_app_diff : forall x y p nu z, z <> x ->
      tm_subst_tm_tm (a_Var_f y) x (a_App p nu (a_Var_f z)) =
      a_App (tm_subst_tm_tm (a_Var_f y) x p) nu (a_Var_f z).
Proof. intros. simpl. f_equal. destruct (z == x). contradiction. auto.
Qed.

(** tmvars and covars in context **)

Fixpoint codom (G : context) :=
   match G with
    | nil => nil
    | (x, Tm _) :: G' => codom G'
    | (c, Co _) :: G' => c :: codom G'
   end.

Fixpoint tmdom (G : context) :=
   match G with
    | nil => nil
    | (x, Tm _) :: G' => x :: tmdom G'
    | (c, Co _) :: G' => tmdom G'
   end.

(** Correctness specification **)

Lemma binds_codom : forall G c phi, binds c (Co phi) G -> In c (codom G).
Proof. intro G. induction G; intros; eauto. inversion H. subst.
       simpl; auto. destruct a. destruct s; simpl. eauto. eauto.
Qed.

Lemma binds_tmdom : forall G x A, binds x (Tm A) G -> In x (tmdom G).
Proof. intro G. induction G; intros; eauto. inversion H. subst.
       simpl; auto. destruct a. destruct s; simpl. eauto. eauto.
Qed.

(** Renaming definitions **)

Definition rename_atom (a b c : atom) : atom := if c == b then a else c.

Definition rename_context_tm (a b : atom) G :=
 List.map 
  (fun zA => (rename_atom a b zA.1, tm_subst_tm_sort (a_Var_f a) b zA.2)) G.

Definition rename_context_co (a b : atom) G :=
 List.map 
  (fun zA => (rename_atom a b zA.1, co_subst_co_sort (g_Var_f a) b zA.2)) G.

Definition rename_role_context (a b : atom) (W : role_context) :=
 List.map (fun zR => (rename_atom a b zR.1, zR.2)) W.

Definition rename_atoms (a b : atom) D :=
  if (AtomSetImpl.mem b D) then singleton a \u (remove b D) else D.


(** Lemmas about renaming atoms **)

Lemma rename_atom_same : forall y a, rename_atom y y a = a.
Proof. intros. unfold rename_atom. destruct (a == y); auto.
Qed.

Lemma rename_atom_diff : forall y a, rename_atom y a a = y.
Proof. intros. unfold rename_atom. destruct (a == a); auto. contradiction.
Qed.

Lemma rename_atom_diff_same : forall x y a, a <> x -> rename_atom y x a = a.
Proof. intros. unfold rename_atom. destruct (a == x); auto. contradiction.
Qed.

(** Lemmas about renamed atoms in contexts **)

Lemma rename_binds_tm : forall G x x0 y s, binds x s G ->
      binds (rename_atom y x0 x) (tm_subst_tm_sort (a_Var_f y) x0 s)
                                              (rename_context_tm y x0 G).
Proof. intro G. induction G; intros; eauto.
       inversion H; subst. simpl. unfold rename_atom.
       destruct (x == x0); eauto. simpl. eauto.
Qed.

Lemma rename_binds_co : forall G x x0 y s, binds x s G ->
      binds (rename_atom y x0 x) (co_subst_co_sort (g_Var_f y) x0 s)
                                 (rename_context_co y x0 G).
Proof. intro G. induction G; intros; eauto.
       inversion H; subst. simpl. unfold rename_atom.
       destruct (x == x0); eauto. simpl. eauto.
Qed.

Lemma rename_context_tm_notin : forall G x y z, x `notin` dom G ->
      y `notin` dom G -> x <> y ->
     (rename_atom y z x) `notin` dom (rename_context_tm y z G).
Proof. induction G; intros. eauto. destruct a; simpl in *.
       unfold rename_atom. destruct (x == z). destruct (a == z).
       subst. assert False. apply H. eauto. contradiction. subst.
       move: (IHG z y z ltac:(auto) ltac:(auto) ltac:(auto)) => h.
       rewrite rename_atom_diff in h. eauto.
       destruct (a == z). subst. eapply notin_add_3. eauto.
       move: (IHG x y z ltac:(auto) ltac:(auto) ltac:(auto)) => h.
       rewrite rename_atom_diff_same in h. auto. auto.
       eapply notin_add_3. eauto.
       move: (IHG x y z ltac:(auto) ltac:(auto) ltac:(auto)) => h.
       rewrite rename_atom_diff_same in h. auto. auto.
Qed.

Lemma rename_context_co_notin : forall G x y z, x `notin` dom G ->
      y `notin` dom G -> x <> y ->
     (rename_atom y z x) `notin` dom (rename_context_co y z G).
Proof. induction G; intros. eauto. destruct a; simpl in *.
       unfold rename_atom. destruct (x == z). destruct (a == z).
       subst. assert False. apply H. eauto. contradiction. subst.
       move: (IHG z y z ltac:(auto) ltac:(auto) ltac:(auto)) => h.
       rewrite rename_atom_diff in h. eauto.
       destruct (a == z). subst. eapply notin_add_3. eauto.
       move: (IHG x y z ltac:(auto) ltac:(auto) ltac:(auto)) => h.
       rewrite rename_atom_diff_same in h. auto. auto.
       eapply notin_add_3. eauto.
       move: (IHG x y z ltac:(auto) ltac:(auto) ltac:(auto)) => h.
       rewrite rename_atom_diff_same in h. auto. auto.
Qed.


(** Renaming PatternContexts **)

Lemma PatternContexts_rename_tm : forall W G D F p A B x y,
      PatternContexts W G D F A p B -> y `notin` dom G -> ~In x (codom G) ->
      PatternContexts (rename_role_context y x W) (rename_context_tm y x G)
       (List.map (rename_atom y x) D) F (tm_subst_tm_tm (a_Var_f y) x A)
       (tm_subst_tm_tm (a_Var_f y) x p) (tm_subst_tm_tm (a_Var_f y) x B).
Proof. intros. induction H.
        - simpl in *. econstructor; eauto with lngen lc.
        - destruct (x0 == x). subst. rewrite tm_subst_tm_tm_open_tm_wrt_tm.
          eauto. rewrite tm_subst_tm_tm_same_diff.
          rewrite tm_subst_tm_tm_app_same_diff. 
          simpl. rewrite rename_atom_diff.
          eapply PatCtx_PiRel with (L := remove y L).
          eauto. eauto. rewrite tm_subst_tm_tm_open_tm_wrt_tm.
          eauto. rewrite tm_subst_tm_tm_diff. auto.
          rewrite tm_subst_tm_tm_app_diff. auto.
          simpl. rewrite rename_atom_diff_same. auto.
          eapply PatCtx_PiRel with (L := remove x0 L).
          eauto. eauto.
        - destruct (x0 == x). subst. rewrite tm_subst_tm_tm_open_tm_wrt_tm.
          eauto. rewrite tm_subst_tm_tm_same_diff.
          simpl. rewrite rename_atom_diff.
          eapply PatCtx_PiIrr with (L := remove y L).
          eauto. eauto. simpl. rewrite rename_atom_diff_same. auto.
          rewrite tm_subst_tm_tm_open_tm_wrt_tm. eauto.
          rewrite (tm_subst_tm_tm_fresh_eq (a_Var_f x0)).
          simpl; auto. eapply PatCtx_PiIrr with (L := remove x0 L).
          eauto. eauto.
        - simpl in *. destruct (c == x). subst.
          assert False. apply H1. eauto. contradiction.
          rewrite rename_atom_diff_same. auto.
          rewrite tm_subst_tm_tm_open_tm_wrt_co. eauto. simpl.
          eapply PatCtx_CPi with (L := remove c L). eauto. auto.
Qed.


Lemma PatternContexts_rename_co : forall W G D F p A B x y,
      PatternContexts W G D F A p B -> y `notin` dom G -> ~In x (tmdom G) ->
      PatternContexts (rename_role_context y x W) (rename_context_co y x G)
       (List.map (rename_atom y x) D) F (co_subst_co_tm (g_Var_f y) x A)
       (co_subst_co_tm (g_Var_f y) x p) (co_subst_co_tm (g_Var_f y) x B).
Proof. intros. induction H; simpl in *.
        - econstructor; eauto with lngen lc.
        - destruct (x0 == x). subst. assert False. apply H1. eauto.
          contradiction. rewrite rename_atom_diff_same. auto.
          rewrite co_subst_co_tm_open_tm_wrt_tm. eauto.
          simpl. eapply PatCtx_PiRel with (L := remove x0 L). eauto. auto.
        - destruct (x0 == x). subst. assert False. apply H1. eauto.
          contradiction. rewrite rename_atom_diff_same. auto.
          rewrite co_subst_co_tm_open_tm_wrt_tm. eauto. simpl.
          eapply PatCtx_PiIrr with (L := remove x0 L). eauto. auto.
        - destruct (c == x) eqn:h. subst.
          rewrite rename_atom_diff. rewrite co_subst_co_tm_open_tm_wrt_co.
          eauto. simpl. destruct (x == x) eqn:h1. rewrite h1.
          eapply PatCtx_CPi with (L := remove y L). eauto. auto.
          contradiction. rewrite co_subst_co_tm_open_tm_wrt_co. eauto.
          simpl. rewrite h. rewrite rename_atom_diff_same. auto.
          eapply PatCtx_CPi with (L := remove c L). eauto. auto.
Qed.

Lemma rename_context_tm_uniq : forall G x y, uniq G -> y `notin` dom G ->
      uniq (rename_context_tm y x G).
Proof. induction G; intros; simpl; eauto 2.
       econstructor. eapply IHG. inversion H; subst. auto.
       destruct a. simpl in H0. fsetdec. destruct a. simpl in *.
       eapply rename_context_tm_notin. inversion H; subst. auto.
       fsetdec. fsetdec.
Qed.

Lemma rename_context_co_uniq : forall G x y, uniq G -> y `notin` dom G ->
      uniq (rename_context_co y x G).
Proof. induction G; intros; simpl; eauto 2.
       econstructor. eapply IHG. inversion H; subst. auto.
       destruct a. simpl in H0. fsetdec. destruct a. simpl in *.
       eapply rename_context_co_notin. inversion H; subst. auto.
       fsetdec. fsetdec.
Qed.

Lemma BranchTyping_rename_tm :
      forall G0 n R b B b2 aa B2 B3 C (H : BranchTyping G0 n R b B b2 aa B2 B3 C),
      forall y x, y `notin` dom G0 -> ~In x (codom G0) ->
                   BranchTyping (rename_context_tm y x G0) n R
                           (tm_subst_tm_tm (a_Var_f y) x b)
                           (tm_subst_tm_tm (a_Var_f y) x B)
                           (tm_subst_tm_tm (a_Var_f y) x b2)
                           (List.map (tm_subst_tm_pattern_arg (a_Var_f y) x) aa)
                           (tm_subst_tm_tm (a_Var_f y) x B2)
                           (tm_subst_tm_tm (a_Var_f y) x B3)
                           (tm_subst_tm_tm (a_Var_f y) x C).
Proof.
  induction 1; intros; subst; simpl.
   - autorewrite with subst_open; eauto 3 with lc.
     rewrite tm_subst_tm_tm_apply_pattern_args.
     eapply BranchTyping_Base; eauto 4 using tm_subst_tm_tm_lc_tm.
     eapply rename_context_tm_uniq; auto.
   - eapply BranchTyping_PiRole with (L := singleton x \u singleton y \u L).
    intros.
    assert (Q : tm_subst_tm_tm (a_Var_f y) x (a_Var_f x0) = a_Var_f x0).
    { rewrite tm_subst_tm_tm_fresh_eq. simpl. auto. auto. }
    simpl in H0. simpl. move: (H0 x0 ltac:(auto) y x ltac:(auto) H2) => h.
    rewrite rename_atom_diff_same in h. auto. rewrite map_app in h.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto. rewrite Q in h.
    simpl in h. destruct (x0 == x) eqn: h1. subst. clear - H3. fsetdec.
    rewrite h1 in h. auto.
   - eapply BranchTyping_PiRel with (L := singleton x \u singleton y \u L).
    intros.
    assert (Q : tm_subst_tm_tm (a_Var_f y) x (a_Var_f x0) = a_Var_f x0).
    { rewrite tm_subst_tm_tm_fresh_eq. simpl. auto. auto. }
    simpl in H0. simpl. move: (H0 x0 ltac:(auto) y x ltac:(auto) H2) => h.
    rewrite rename_atom_diff_same in h. auto. rewrite map_app in h.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto. rewrite Q in h.
    simpl in h. destruct (x0 == x) eqn: h1. subst. clear - H3. fsetdec.
    rewrite h1 in h. auto.
   - eapply BranchTyping_PiIrrel with (L := singleton x \u singleton y \u L).
    intros.
    assert (Q : tm_subst_tm_tm (a_Var_f y) x (a_Var_f x0) = a_Var_f x0).
    { rewrite tm_subst_tm_tm_fresh_eq. simpl. auto. auto. }
    simpl in H0. simpl. move: (H0 x0 ltac:(auto) y x ltac:(auto) H2) => h.
    rewrite rename_atom_diff_same in h. auto. rewrite map_app in h.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto.
    rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto. rewrite Q in h.
    simpl in h. auto.
   - eapply BranchTyping_CPi with (L := singleton x \u singleton y \u L). intros.
    simpl in H0. simpl. move: (H0 c ltac:(auto) y x) => h.
    rewrite rename_atom_diff_same in h. auto. rewrite map_app in h.
    rewrite tm_subst_tm_tm_open_tm_wrt_co in h. eauto.
    rewrite tm_subst_tm_tm_open_tm_wrt_co in h. eauto.
    simpl in h. eapply h. clear - H1 H3. fsetdec. intro.
    inversion H4. subst. clear - H3. fsetdec. auto.
Qed.

Lemma BranchTyping_rename_co :
      forall G0 n R b B b2 aa B2 B3 C (H : BranchTyping G0 n R b B b2 aa B2 B3 C),
      forall y x, y `notin` dom G0 -> ~In x (tmdom G0) ->
                   BranchTyping (rename_context_co y x G0) n R
                           (co_subst_co_tm (g_Var_f y) x b)
                           (co_subst_co_tm (g_Var_f y) x B)
                           (co_subst_co_tm (g_Var_f y) x b2)
                           (List.map (co_subst_co_pattern_arg (g_Var_f y) x) aa)
                           (co_subst_co_tm (g_Var_f y) x B2)
                           (co_subst_co_tm (g_Var_f y) x B3)
                           (co_subst_co_tm (g_Var_f y) x C).
Proof.
  induction 1; intros; subst; simpl.
   - autorewrite with subst_open; eauto 3 with lc.
     rewrite co_subst_co_tm_apply_pattern_args.
     eapply BranchTyping_Base; eauto 4 using co_subst_co_tm_lc_tm.
     eapply rename_context_co_uniq; auto.
   - eapply BranchTyping_PiRole with (L := singleton x \u singleton y \u L).
    intros.
    simpl in H0. simpl. move: (H0 x0 ltac:(auto) y x ltac:(auto)) => h.
    rewrite rename_atom_diff_same in h. auto. rewrite map_app in h.
    rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
    rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
    simpl in h. eapply h. intro. inversion H4. subst. clear - H3. fsetdec.
    contradiction.
   - eapply BranchTyping_PiRel with (L := singleton x \u singleton y \u L).
    intros.
    simpl in H0. simpl. move: (H0 x0 ltac:(auto) y x ltac:(auto)) => h.
    rewrite rename_atom_diff_same in h. auto. rewrite map_app in h.
    rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
    rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
    simpl in h. eapply h. intro. inversion H4. subst. clear - H3. fsetdec.
    contradiction.
   - eapply BranchTyping_PiIrrel with (L := singleton x \u singleton y \u L).
    intros.
    simpl in H0. simpl. move: (H0 x0 ltac:(auto) y x ltac:(auto)) => h.
    rewrite rename_atom_diff_same in h. auto. rewrite map_app in h.
    rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
    rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
    simpl in h. eapply h. intro. inversion H4. subst. clear - H3. fsetdec.
    contradiction.
   - eapply BranchTyping_CPi with (L := singleton x \u singleton y \u L). intros.
    assert (Q : co_subst_co_co (g_Var_f y) x (g_Var_f c) = g_Var_f c).
    { rewrite co_subst_co_co_fresh_eq. simpl. auto. auto. }
    simpl in H0. simpl. move: (H0 c ltac:(auto) y x) => h.
    rewrite rename_atom_diff_same in h. auto. rewrite map_app in h.
    rewrite co_subst_co_tm_open_tm_wrt_co in h. eauto.
    rewrite co_subst_co_tm_open_tm_wrt_co in h. eauto. rewrite Q in h.
    simpl in h. eapply h. clear - H1 H3. fsetdec. apply H2.
Qed.

Lemma tm_rename_mutual :
   (forall G b B (H : Typing G b B),
      forall x y, y `notin` dom G -> ~In x (codom G) ->
        Typing (rename_context_tm y x G)
               (tm_subst_tm_tm (a_Var_f y) x b)
               (tm_subst_tm_tm (a_Var_f y) x B)) /\
    (forall G phi  (H : PropWff G phi),
       forall x y, y `notin` dom G -> ~In x (codom G) ->
        PropWff (rename_context_tm y x G)
                (tm_subst_tm_constraint (a_Var_f y) x phi) ) /\
    (forall G D p1 p2  (H : Iso G D p1 p2 ),
       forall x y, y `notin` dom G -> ~In x (codom G) ->
        Iso (rename_context_tm y x G) D
            (tm_subst_tm_constraint (a_Var_f y) x p1)
            (tm_subst_tm_constraint (a_Var_f y) x p2) ) /\
    (forall G D A B T R (H : DefEq G D A B T R),
       forall x y, y `notin` dom G -> ~In x (codom G) ->
         DefEq (rename_context_tm y x G) D
               (tm_subst_tm_tm (a_Var_f y) x A) (tm_subst_tm_tm (a_Var_f y) x B)
               (tm_subst_tm_tm (a_Var_f y) x T) R) /\
    (forall G (H : Ctx G),
        forall x y, y `notin` dom G -> ~In x (codom G) ->
                        Ctx (rename_context_tm y x G)).
Proof. ext_induction CON; intros; subst; simpl.
        - eauto.
        - move: (rename_binds_tm G x x0 y (Tm A) b) => h.
          destruct (x == x0); econstructor. eauto. subst.
          rewrite rename_atom_diff in h. auto. eauto.
          rewrite rename_atom_diff_same in h; auto.
        - eapply E_Pi with (L := singleton y \u singleton x \u L); eauto.
          intros. move: (H x0 ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto.
          rewrite (tm_subst_tm_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. apply h; auto.
        - eapply E_Abs with
             (L := singleton y \u singleton x \u L); eauto.
          intros. move: (H x0 ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto.
          rewrite (tm_subst_tm_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto.
          rewrite (tm_subst_tm_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. apply h; auto.
          intros. destruct rho. eauto.
          replace (a_Var_f x0) with (tm_subst_tm_tm (a_Var_f y) x (a_Var_f x0)).
          rewrite <- tm_subst_tm_tm_open_tm_wrt_tm. econstructor.
          rewrite fv_tm_tm_tm_tm_subst_tm_tm_upper.
          move: (r x0 ltac:(auto)) => h. inversion h; subst. eauto. eauto.
          apply tm_subst_tm_tm_fresh_eq; eauto.
        - rewrite tm_subst_tm_tm_open_tm_wrt_tm; eauto.
        - rewrite tm_subst_tm_tm_open_tm_wrt_tm. eauto.
          econstructor; eauto. eapply RolePath_subst; eauto.
        - rewrite tm_subst_tm_tm_open_tm_wrt_tm; eauto.
        - econstructor; eauto.
        - eapply E_CPi with (L := singleton y \u singleton x \u L); eauto.
          intros. move: (H c ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite tm_subst_tm_tm_open_tm_wrt_co in h. eauto.
          rewrite (tm_subst_tm_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. apply h. auto. intro. inversion H4. eauto.
          contradiction.
        - eapply E_CAbs with (L := singleton y \u singleton x \u L); eauto.
          intros. move: (H c ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite tm_subst_tm_tm_open_tm_wrt_co in h. eauto.
          rewrite (tm_subst_tm_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. rewrite tm_subst_tm_tm_open_tm_wrt_co in h. eauto.
          rewrite (tm_subst_tm_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. apply h. auto. intro h1. inversion h1. eauto.
          contradiction.
        - simpl in *. rewrite tm_subst_tm_tm_open_tm_wrt_co; eauto.
        - simpl in *. eapply E_Const. eauto.
          rewrite tm_subst_tm_tm_fresh_eq. apply Typing_context_fv in t.
          inversion t. simpl in H3. rewrite H3. all: eauto.
        - simpl in *. eapply E_Fam. eauto.
          rewrite tm_subst_tm_tm_fresh_eq. apply Typing_context_fv in t.
          inversion t. simpl in H3. rewrite H3. all: eauto.
        - eapply E_Case. eauto. eauto. eauto.
          replace (a_Fam F) with (tm_subst_tm_tm (a_Var_f y) x (a_Fam F)).
          replace nil with (List.map (tm_subst_tm_pattern_arg (a_Var_f y) x) nil).
          eapply BranchTyping_rename_tm. eapply b. auto. auto. simpl. auto.
          auto. eauto. auto.
        - eapply E_Wff; eauto.
        - eapply E_PropCong; eauto.
        - eapply E_IsoConv; eauto.
        - simpl in *. eapply E_CPiFst; eauto.
        - eapply E_Assn. eauto.
          move: (rename_binds_tm G c x y (Co (Eq a b A R)) b0) => h.
          rewrite rename_atom_diff_same in h. intro. subst. apply H1.
          eapply binds_codom. eauto. simpl in h. eauto. eauto.
        - eapply E_Refl; eauto.
        - eapply E_Sym; eauto.
        - eapply E_Trans; eauto.
        - eapply E_Sub; eauto.
        - eapply E_Beta. eauto. eauto. eapply Beta_tm_subst. auto. eauto.
        - eapply E_PiCong with (L := singleton y \u singleton x \u L). eauto.
          intros. move: (H0 x0 ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto.
          rewrite (tm_subst_tm_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto.
          rewrite (tm_subst_tm_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. apply h; auto. all: eauto.
        - eapply E_AbsCong with (L := singleton y \u singleton x \u L).
          + intros. move: (H x0 ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto.
          rewrite (tm_subst_tm_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto.
          rewrite (tm_subst_tm_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto.
          rewrite (tm_subst_tm_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. apply h; auto.
          + eauto.
          + intros. destruct rho. eauto.
          replace (a_Var_f x0) with (tm_subst_tm_tm (a_Var_f y) x (a_Var_f x0)).
          rewrite <- tm_subst_tm_tm_open_tm_wrt_tm. econstructor.
          rewrite fv_tm_tm_tm_tm_subst_tm_tm_upper.
          move: (r x0 ltac:(auto)) => h. inversion h; subst. eauto. eauto.
          apply tm_subst_tm_tm_fresh_eq; eauto.
          + intros. destruct rho. eauto.
          replace (a_Var_f x0) with (tm_subst_tm_tm (a_Var_f y) x (a_Var_f x0)).
          rewrite <- tm_subst_tm_tm_open_tm_wrt_tm. econstructor.
          rewrite fv_tm_tm_tm_tm_subst_tm_tm_upper.
          move: (r0 x0 ltac:(auto)) => h. inversion h; subst. eauto. eauto.
          apply tm_subst_tm_tm_fresh_eq; eauto.
        - rewrite tm_subst_tm_tm_open_tm_wrt_tm. eauto.
          eapply E_AppCong; eauto.
        - rewrite tm_subst_tm_tm_open_tm_wrt_tm. eauto.
          eapply E_TAppCong. 2:eauto. eapply H; eauto.
          eapply RolePath_subst; eauto. eapply RolePath_subst; eauto.
          simpl in H1. move: (H1 x y) => h1.
          rewrite tm_subst_tm_tm_open_tm_wrt_tm in h1. eauto. eauto.
        - rewrite tm_subst_tm_tm_open_tm_wrt_tm. eauto.
          eapply E_IAppCong; eauto.
        - eapply E_PiFst; eauto.
        - rewrite tm_subst_tm_tm_open_tm_wrt_tm. eauto.
          rewrite tm_subst_tm_tm_open_tm_wrt_tm. eauto.
          eapply E_PiSnd; eauto.
        - eapply E_CPiCong with (L := singleton y \u singleton x \u L). eauto.
          intros. move: (H0 c ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite tm_subst_tm_tm_open_tm_wrt_co in h. eauto.
          rewrite (tm_subst_tm_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. rewrite tm_subst_tm_tm_open_tm_wrt_co in h. eauto.
          rewrite (tm_subst_tm_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. apply h; auto. eauto. all: simpl in *; eauto.
          intro h1. inversion h1. eauto. contradiction.
        - eapply E_CAbsCong with (L := singleton y \u singleton x \u L).
          intros. move: (H c ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite tm_subst_tm_tm_open_tm_wrt_co in h. eauto.
          rewrite (tm_subst_tm_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. rewrite tm_subst_tm_tm_open_tm_wrt_co in h. eauto.
          rewrite (tm_subst_tm_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. rewrite tm_subst_tm_tm_open_tm_wrt_co in h. eauto.
          rewrite (tm_subst_tm_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. apply h; auto.
          intro h1. inversion h1. eauto. contradiction. eauto.
        - rewrite tm_subst_tm_tm_open_tm_wrt_co. eauto.
          eapply E_CAppCong. simpl in *; eauto. eauto.
        - rewrite tm_subst_tm_tm_open_tm_wrt_co. eauto.
          rewrite tm_subst_tm_tm_open_tm_wrt_co. eauto.
          eapply E_CPiSnd. simpl in *; eauto. eauto. eauto.
        - eapply E_Cast. eapply H; eauto. simpl in *. eapply H0; eauto.
        - eapply E_EqConv; eauto.
        - eapply E_IsoSnd; eauto.
        - eapply E_PatCong. eauto. eauto. eauto.
          replace (a_Fam F) with (tm_subst_tm_tm (a_Var_f y) x (a_Fam F)).
          replace nil with (List.map (tm_subst_tm_pattern_arg (a_Var_f y) x) nil).
          eapply BranchTyping_rename_tm. eapply b. auto. auto. simpl. auto.
          auto.
          replace (a_Fam F) with (tm_subst_tm_tm (a_Var_f y) x (a_Fam F)).
          replace nil with (List.map (tm_subst_tm_pattern_arg (a_Var_f y) x) nil).
          eapply BranchTyping_rename_tm. eapply b0. auto. auto. simpl. auto.
          auto. all:eauto.
        - eapply E_LeftRel.
          move: (CasePath_subst_tm x c (lc_a_Var_f y)) => h.
          eauto. move: (CasePath_subst_tm x c0 (lc_a_Var_f y)) => h0. eauto.
          eauto. eauto. eauto. eauto.
          move: (H3 x y ltac:(auto) ltac:(auto)) => h. 
          rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto. eapply h.
          move: (H4 x y ltac:(auto) ltac:(auto)) => h.
          rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto.
          rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto. eauto.
        - eapply E_LeftIrrel.
          move: (CasePath_subst_tm x c (lc_a_Var_f y)) => h.
          eauto. move: (CasePath_subst_tm x c0 (lc_a_Var_f y)) => h0. eauto.
          eauto. eauto. eauto. eauto.
          move: (H3 x y ltac:(auto) ltac:(auto)) => h. 
          rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto. eapply h.
          move: (H4 x y ltac:(auto) ltac:(auto)) => h.
          rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto.
          rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto. eauto.
        - eapply E_Right.
          move: (CasePath_subst_tm x c (lc_a_Var_f y)) => h.
          eauto. move: (CasePath_subst_tm x c0 (lc_a_Var_f y)) => h0. eauto.
          eauto. eauto. eauto. eauto.
          move: (H3 x y ltac:(auto) ltac:(auto)) => h. 
          rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto. eapply h.
          move: (H4 x y ltac:(auto) ltac:(auto)) => h.
          rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto.
          rewrite tm_subst_tm_tm_open_tm_wrt_tm in h. eauto. eauto.
        - eapply E_CLeft.
          move: (CasePath_subst_tm x c (lc_a_Var_f y)) => h.
          eauto. move: (CasePath_subst_tm x c0 (lc_a_Var_f y)) => h0. eauto.
          simpl in *; eauto. simpl in *; eauto. eauto.
          move: (H2 x y ltac:(auto) ltac:(auto)) => h.
          rewrite tm_subst_tm_tm_open_tm_wrt_co in h. eauto.
          simpl in *; eauto.
        - eauto.
        - econstructor. eapply H; eauto. eauto.
          apply rename_context_tm_notin; auto.
        - simpl in *. eapply E_ConsCo. eauto. eauto.
          apply rename_context_tm_notin; auto.
Qed.

Lemma co_rename_mutual :
   (forall G b B (H : Typing G b B),
      forall x y, y `notin` dom G -> ~In x (tmdom G) ->
        Typing (rename_context_co y x G)
               (co_subst_co_tm (g_Var_f y) x b)
               (co_subst_co_tm (g_Var_f y) x B)) /\
    (forall G phi  (H : PropWff G phi),
       forall x y, y `notin` dom G -> ~In x (tmdom G) ->
        PropWff (rename_context_co y x G)
                (co_subst_co_constraint (g_Var_f y) x phi) ) /\
    (forall G D p1 p2  (H : Iso G D p1 p2 ),
       forall x y, y `notin` dom G -> ~In x (tmdom G) ->
        Iso (rename_context_co y x G) (rename_atoms y x D)
            (co_subst_co_constraint (g_Var_f y) x p1)
            (co_subst_co_constraint (g_Var_f y) x p2) ) /\
    (forall G D A B T R (H : DefEq G D A B T R),
       forall x y, y `notin` dom G -> ~In x (tmdom G) ->
         DefEq (rename_context_co y x G) (rename_atoms y x D)
               (co_subst_co_tm (g_Var_f y) x A) (co_subst_co_tm (g_Var_f y) x B)
               (co_subst_co_tm (g_Var_f y) x T) R) /\
    (forall G (H : Ctx G),
        forall x y, y `notin` dom G -> ~In x (tmdom G) ->
                        Ctx (rename_context_co y x G)).
Proof. ext_induction CON; intros; subst; simpl.
        - eauto.
        - move: (rename_binds_co G x x0 y (Tm A) b) => h.
          destruct (x == x0). subst. assert False. apply H1.
          eapply binds_tmdom. eauto. contradiction.
          rewrite rename_atom_diff_same in h; auto.
        - eapply E_Pi with (L := singleton y \u singleton x \u L); eauto.
          intros. move: (H x0 ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
          rewrite (co_subst_co_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. apply h; auto.
          intro h1. inversion h1. eauto. contradiction.
        - eapply E_Abs with
             (L := singleton y \u singleton x \u L); eauto.
          intros. move: (H x0 ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
          rewrite (co_subst_co_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
          rewrite (co_subst_co_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. apply h; auto.
          intro h1. inversion h1. eauto. contradiction.
          intros. destruct rho. eauto.
          replace (a_Var_f x0) with (co_subst_co_tm (g_Var_f y) x (a_Var_f x0)).
          rewrite <- co_subst_co_tm_open_tm_wrt_tm. econstructor.
          rewrite fv_tm_tm_tm_co_subst_co_tm_upper.
          move: (r x0 ltac:(auto)) => h. inversion h; subst. eauto. eauto.
          apply co_subst_co_tm_fresh_eq; eauto.
        - rewrite co_subst_co_tm_open_tm_wrt_tm; eauto.
        - rewrite co_subst_co_tm_open_tm_wrt_tm. eauto.
          econstructor; eauto. eapply RolePath_subst_co; eauto.
        - rewrite co_subst_co_tm_open_tm_wrt_tm; eauto.
        - econstructor; eauto.
        - eapply E_CPi with (L := singleton y \u singleton x \u L); eauto.
          intros. move: (H c ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_co in h. eauto.
          rewrite (co_subst_co_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. apply h; auto.
        - eapply E_CAbs with (L := singleton y \u singleton x \u L); eauto.
          intros. move: (H c ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_co in h. eauto.
          rewrite (co_subst_co_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. rewrite co_subst_co_tm_open_tm_wrt_co in h. eauto.
          rewrite (co_subst_co_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. apply h; auto.
        - simpl in *. rewrite co_subst_co_tm_open_tm_wrt_co; eauto.
        - simpl in *. eapply E_Const. eauto.
          rewrite co_subst_co_tm_fresh_eq. apply Typing_context_fv in t.
          inversion t. inversion H4. rewrite H5. all: eauto.
        - simpl in *. eapply E_Fam. eauto.
          rewrite co_subst_co_tm_fresh_eq. apply Typing_context_fv in t.
          inversion t. inversion H4. rewrite H5. all: eauto.
        - eapply E_Case. eauto. eauto. eauto.
          replace (a_Fam F) with (co_subst_co_tm (g_Var_f y) x (a_Fam F)).
          replace nil with (List.map (co_subst_co_pattern_arg (g_Var_f y) x) nil).
          eapply BranchTyping_rename_co. eapply b. auto. auto. simpl. auto.
          auto. eauto. auto.
        - eapply E_Wff; eauto.
        - eapply E_PropCong; eauto.
        - eapply E_IsoConv; eauto.
        - simpl in *. eapply E_CPiFst; eauto.
        - move: (rename_binds_co G c x y (Co (Eq a b A R)) b0) => h.
          unfold rename_atoms. destruct (c == x).
          + subst. rewrite rename_atom_diff in h.
          destruct (AtomSetImpl.mem x D) eqn:h1. eapply E_Assn. eauto.
          simpl in *. eauto. eauto. apply not_mem_iff in h1.
          contradiction.
          + rewrite rename_atom_diff_same in h. auto.
          destruct (AtomSetImpl.mem x D). eapply E_Assn. eauto.
          simpl in *. eauto. fsetdec. eapply E_Assn. eauto. simpl in *.
          eauto. eauto.
        - eapply E_Refl; eauto.
        - eapply E_Sym; eauto.
        - eapply E_Trans; eauto.
        - eapply E_Sub; eauto.
        - eapply E_Beta. eauto. eauto. eapply Beta_co_subst. auto. eauto.
        - eapply E_PiCong with (L := singleton y \u singleton x \u L). eauto.
          intros. move: (H0 x0 ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
          rewrite (co_subst_co_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
          rewrite (co_subst_co_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. apply h; auto. all: eauto.
          intro h1. inversion h1. eauto. contradiction.
        - eapply E_AbsCong with (L := singleton y \u singleton x \u L).
          + intros. move: (H x0 ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
          rewrite (co_subst_co_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
          rewrite (co_subst_co_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
          rewrite (co_subst_co_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. apply h; auto.
          intro h1. inversion h1. eauto. contradiction.
          + eauto.
          + intros. destruct rho. eauto.
          replace (a_Var_f x0) with (co_subst_co_tm (g_Var_f y) x (a_Var_f x0)).
          rewrite <- co_subst_co_tm_open_tm_wrt_tm. econstructor.
          rewrite fv_tm_tm_tm_co_subst_co_tm_upper.
          move: (r x0 ltac:(auto)) => h. inversion h; subst. eauto. eauto.
          apply co_subst_co_tm_fresh_eq; eauto.
          + intros. destruct rho. eauto.
          replace (a_Var_f x0) with (co_subst_co_tm (g_Var_f y) x (a_Var_f x0)).
          rewrite <- co_subst_co_tm_open_tm_wrt_tm. econstructor.
          rewrite fv_tm_tm_tm_co_subst_co_tm_upper.
          move: (r0 x0 ltac:(auto)) => h. inversion h; subst. eauto. eauto.
          apply co_subst_co_tm_fresh_eq; eauto.
        - rewrite co_subst_co_tm_open_tm_wrt_tm. eauto.
          eapply E_AppCong; eauto.
        - rewrite co_subst_co_tm_open_tm_wrt_tm. eauto.
          eapply E_TAppCong. 2:eauto. eapply H; eauto.
          eapply RolePath_subst_co; eauto. eapply RolePath_subst_co; eauto.
          simpl in H1. move: (H1 x y) => h1.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h1. eauto. eauto.
        - rewrite co_subst_co_tm_open_tm_wrt_tm. eauto.
          eapply E_IAppCong; eauto.
        - eapply E_PiFst; eauto.
        - rewrite co_subst_co_tm_open_tm_wrt_tm. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_tm. eauto.
          eapply E_PiSnd; eauto.
        - eapply E_CPiCong with (L := singleton y \u singleton x \u L). eauto.
          intros. move: (H0 c ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_co in h. eauto.
          rewrite (co_subst_co_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. rewrite co_subst_co_tm_open_tm_wrt_co in h. eauto.
          rewrite (co_subst_co_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. apply h; auto. eauto. all: simpl in *; eauto.
        - eapply E_CAbsCong with (L := singleton y \u singleton x \u L).
          intros. move: (H c ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_co in h. eauto.
          rewrite (co_subst_co_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. rewrite co_subst_co_tm_open_tm_wrt_co in h. eauto.
          rewrite (co_subst_co_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. rewrite co_subst_co_tm_open_tm_wrt_co in h. eauto.
          rewrite (co_subst_co_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. apply h; auto. eauto.
        - rewrite co_subst_co_tm_open_tm_wrt_co. eauto.
          eapply E_CAppCong. simpl in *; eauto. eauto.
        - rewrite co_subst_co_tm_open_tm_wrt_co. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_co. eauto.
          eapply E_CPiSnd. simpl in *; eauto. eauto. eauto.
        - eapply E_Cast. eapply H; eauto. simpl in *. eapply H0; eauto.
        - eapply E_EqConv; eauto.
        - eapply E_IsoSnd; eauto.
        - eapply E_PatCong. eauto. eauto. eauto.
          replace (a_Fam F) with (co_subst_co_tm (g_Var_f y) x (a_Fam F)).
          replace nil with (List.map (co_subst_co_pattern_arg (g_Var_f y) x) nil).
          eapply BranchTyping_rename_co. eapply b. auto. auto. simpl. auto.
          auto.
          replace (a_Fam F) with (co_subst_co_tm (g_Var_f y) x (a_Fam F)).
          replace nil with (List.map (co_subst_co_pattern_arg (g_Var_f y) x) nil).
          eapply BranchTyping_rename_co. eapply b0. auto. auto. simpl. auto.
          auto. all:eauto.
        - eapply E_LeftRel.
          move: (CasePath_subst_co x c (lc_g_Var_f y)) => h.
          eauto. move: (CasePath_subst_co x c0 (lc_g_Var_f y)) => h0. eauto.
          eauto. eauto. eauto. eauto.
          move: (H3 x y ltac:(auto) ltac:(auto)) => h. 
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto. eapply h.
          move: (H4 x y ltac:(auto) ltac:(auto)) => h.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto. eauto.
        - eapply E_LeftIrrel.
          move: (CasePath_subst_co x c (lc_g_Var_f y)) => h.
          eauto. move: (CasePath_subst_co x c0 (lc_g_Var_f y)) => h0. eauto.
          eauto. eauto. eauto. eauto.
          move: (H3 x y ltac:(auto) ltac:(auto)) => h. 
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto. eapply h.
          move: (H4 x y ltac:(auto) ltac:(auto)) => h.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto. eauto.
        - eapply E_Right.
          move: (CasePath_subst_co x c (lc_g_Var_f y)) => h.
          eauto. move: (CasePath_subst_co x c0 (lc_g_Var_f y)) => h0. eauto.
          eauto. eauto. eauto. eauto.
          move: (H3 x y ltac:(auto) ltac:(auto)) => h. 
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto. eapply h.
          move: (H4 x y ltac:(auto) ltac:(auto)) => h.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto. eauto.
        - eapply E_CLeft.
          move: (CasePath_subst_co x c (lc_g_Var_f y)) => h.
          eauto. move: (CasePath_subst_co x c0 (lc_g_Var_f y)) => h0. eauto.
          simpl in *; eauto. simpl in *; eauto. eauto.
          move: (H2 x y ltac:(auto) ltac:(auto)) => h.
          rewrite co_subst_co_tm_open_tm_wrt_co in h. eauto.
          simpl in *; eauto.
        - eauto.
        - simpl in *. eapply E_ConsTm. eauto. eauto.
          apply rename_context_co_notin; auto.
        - econstructor. eapply H; eauto. eauto.
          apply rename_context_co_notin; auto.
          Unshelve. all: eauto.
Qed.

(** Some useful functions and propositions **)

Fixpoint left_list A B (l : list (A * B)) :=
   match l with
   | nil => nil
   | (y, x) :: l' => y :: (left_list l')
   end.

Fixpoint right_list A B (l : list (A * B)) :=
   match l with
   | nil => nil
   | (y, x) :: l' => x :: (right_list l')
   end.

Definition disj_list_set l s := forall x, In x l -> x `notin` s.

Definition disj_list_list (l1 l2 : list atom) := forall x, In x l1 -> ~In x l2.


(** List renaming of tmvars
-------------------------------------------------------------
-------------------------------------------------------------
 **)


(* Definitions *)

Definition list_rename_atom l (a : atom) :=
  fold_left (fun z yx => rename_atom yx.1 yx.2 z) l a.

Definition list_rename_tm l (A : tm) :=
   fold_left (fun z yx => tm_subst_tm_tm (a_Var_f yx.1) yx.2 z) l A.

Definition list_rename_context_tm l (G : context) :=
   fold_left (fun G' yx => rename_context_tm yx.1 yx.2 G') l G.

(* ------------------------------------------------------------------ *)

(* Lemmas on domains and codoms of singly renamed and list-renamed contexts *)

Lemma rename_context_tm_dom : forall G x y,
      (forall z, z `in` dom (rename_context_tm y x G) -> z `in` dom G \/ z = y).
Proof. induction G; intros; eauto. destruct a. simpl in *.
       apply add_iff in H. inversion H; clear H.
       - unfold rename_atom in H0.
         destruct (a == x). subst. auto.
         subst. auto.
       - move: (IHG x y z H0) => h. inversion h; auto.
Qed.

Lemma rename_context_tm_codom : forall G x y,
      (forall z, In z (codom (rename_context_tm y x G)) ->
                                  In z (codom G) \/ z = y).
Proof. induction G; intros; eauto. destruct a. destruct s; simpl in *. eauto.
       inversion H; clear H.
       - unfold rename_atom in H0.
         destruct (a == x). apply singleton_iff in H0. subst. auto.
         apply singleton_iff in H0. subst. auto. auto.
       - move: (IHG x y z H0) => h. inversion h; auto.
Qed.

Lemma list_rename_context_tm_dom : forall l G,
      (forall x, x `in` dom (list_rename_context_tm l G) ->
                      x `in` dom G \/ In x (left_list l)).
Proof. induction l; eauto.
       intros. destruct a. simpl in *.
       move: (IHl (rename_context_tm a a0 G) x H) => h.
       inversion h; clear h. apply rename_context_tm_dom in H0.
       inversion H0; auto. auto.
Qed.

Lemma list_rename_context_tm_codom : forall l G,
      (forall x, In x (codom (list_rename_context_tm l G)) ->
                      In x (codom G) \/ In x (left_list l)).
Proof. induction l; eauto.
       intros. destruct a. simpl in *.
       move: (IHl (rename_context_tm a a0 G) x H) => h.
       inversion h; clear h. apply rename_context_tm_codom in H0.
       inversion H0; auto. auto.
Qed.

(* ------------------------------------------------------------- *)

(* Lemmas on commutativity of two rename operations for atoms, sorts, contexts *)

(* Note :- The corresponding lemma for tms is subst_commute_tm from ett_rename.v *)

Lemma rename_atom_commute : forall x1 y1 x2 y2 a,
      x2 <> x1 -> x2 <> y1 -> y2 <> x1 ->
      rename_atom y1 x1 (rename_atom y2 x2 a) =
      rename_atom y2 x2 (rename_atom y1 x1 a).
Proof. intros. unfold rename_atom.
       destruct (a == x2).
        - destruct (y2 == x1).
          + destruct (a == x1).
            * destruct (y1 == x2).
              symmetry in e2. contradiction. (* uses x2 <> y1 *)
              auto.
            * destruct (a == x2). contradiction. (* uses y2 <> x1 *)
              contradiction. (* uses y2 <> x1 *)
          + destruct (a == x1).
            * destruct (y1 == x2).
              auto. rewrite e in e0. contradiction. (* uses x2 <> x1 *)
            * destruct (a == x2). auto. contradiction. (* uses y2 <> x1 *)
        - destruct (a == x1).
           + destruct (y1 == x2).
             symmetry in e0. contradiction. (* uses x2 <> y1 *) auto.
           + destruct (a == x2). contradiction. auto.
Qed.

Lemma subst_commute_sort_tm : forall s a1 a2 x1 x2, x1 `notin` fv_tm_tm_tm a2 ->
      x2 `notin` fv_tm_tm_tm a1 -> x1 <> x2 ->
      tm_subst_tm_sort a2 x2 (tm_subst_tm_sort a1 x1 s) =
      tm_subst_tm_sort a1 x1 (tm_subst_tm_sort a2 x2 s).
Proof. induction s; intros; simpl. f_equal. apply subst_commute_tm; auto.
       f_equal. eapply subst_commute; eauto.
Qed.

Lemma rename_context_commute_tm :  forall G x1 y1 x2 y2,
      x2 <> x1 -> x2 <> y1 -> y2 <> x1 ->
      rename_context_tm y1 x1 (rename_context_tm y2 x2 G) =
      rename_context_tm y2 x2 (rename_context_tm y1 x1 G).
Proof. induction G; intros; eauto. destruct a. simpl in *.
       f_equal. rewrite rename_atom_commute; eauto.
       rewrite subst_commute_sort_tm; eauto. eauto.
Qed.

(* ------------------------------------------------------------- *)

(* Lemmas on commutativity of list-renaming and a single rename on atoms, tms
   and contexts *)

Lemma list_rename_rename_commute_atom : forall l x y a,
      ~In x (left_list l) -> ~In x (right_list l) -> ~In y (right_list l) ->
       list_rename_atom l (rename_atom y x a) =
       rename_atom y x (list_rename_atom l a).
Proof. induction l; intros; eauto. destruct a. simpl in *.
       rewrite rename_atom_commute; eauto. eapply IHl; eauto.
Qed.

Lemma list_rename_rename_commute_tm : forall l x y b,
      ~In x (left_list l) -> ~In x (right_list l) -> ~In y (right_list l) ->
      list_rename_tm l (tm_subst_tm_tm (a_Var_f y) x b) =
      tm_subst_tm_tm (a_Var_f y) x (list_rename_tm l b).
Proof. induction l; intros; eauto.
       destruct a; simpl in *. rewrite subst_commute_tm.
       simpl; eauto. simpl; eauto. eauto. eapply IHl; eauto.
Qed.

Lemma list_rename_rename_commute_context_tm : forall l x y G,
      ~In x (left_list l) -> ~In x (right_list l) -> ~In y (right_list l) ->
      list_rename_context_tm l (rename_context_tm y x G) =
      rename_context_tm y x (list_rename_context_tm l G).
Proof. induction l; intros; eauto. destruct a. simpl in *.
       rewrite rename_context_commute_tm; eauto. eapply IHl; eauto.
Qed.

(* ----------------------------------------------------------- *)

(** Main tmvars renaming lemma **)

Lemma list_tm_rename_typing :
    forall l G, NoDup (left_list l) -> NoDup (right_list l) ->
                disj_list_list (left_list l) (right_list l) ->
                disj_list_set (left_list l) (dom G) ->
                disj_list_list (right_list l) (codom G) ->
    (forall b B (H : Typing G b B),
        Typing (list_rename_context_tm l G)
               (list_rename_tm l b)
               (list_rename_tm l B)).
Proof. induction l; intros; eauto.
       destruct a; simpl in *.
       unfold disj_list_list in *. unfold disj_list_set in *.
       rewrite list_rename_rename_commute_tm. intro. apply (H1 a0).
       simpl; auto. simpl; auto. inversion H0; subst; auto.
       intro. apply (H1 a). simpl; auto. simpl; auto.
       rewrite list_rename_rename_commute_tm. intro. apply (H1 a0).
       simpl; auto. simpl; auto. inversion H0; subst; auto.
       intro. apply (H1 a). simpl; auto. simpl; auto.
       rewrite list_rename_rename_commute_context_tm.
       intro. apply (H1 a0). simpl; auto. simpl; auto.
       inversion H0; subst; auto. intro. apply (H1 a). simpl; auto. simpl; auto.
       eapply tm_rename_mutual. eapply IHl.
       inversion H; subst; eauto. inversion H0; subst; eauto.
       intros. intro. apply (H1 x). simpl; auto. simpl; auto.
       intros. intro. apply (H2 x). simpl; auto. auto.
       intros. intro. apply (H3 x). simpl; auto. auto. auto.
       intro. apply list_rename_context_tm_dom in H5. inversion H5; clear H5.
       apply (H2 a). simpl; auto. auto. inversion H; subst; auto.
       intro. apply list_rename_context_tm_codom in H5. inversion H5; clear H5.
       apply (H3 a0). simpl; auto. auto. apply (H1 a0). simpl; auto. simpl; auto.
Qed.

(** ------------------------------------------------------------------
    ------------------------------------------------------------------
 **)


(** List renaming of covars
-------------------------------------------------------------
-------------------------------------------------------------
 **)


(* Definitions *)

Definition list_rename_co (l : list (atom * atom)) (A : tm) :=
   fold_left (fun z yx => co_subst_co_tm (g_Var_f yx.1) yx.2 z) l A.

Definition list_rename_context_co l (G : context) :=
   fold_left (fun G' yx => rename_context_co yx.1 yx.2 G') l G.


(* ------------------------------------------------------------------ *)

(* Lemmas on domains and tmdoms of singly renamed and list-renamed contexts *)

Lemma rename_context_co_dom : forall G x y,
      (forall z, z `in` dom (rename_context_co y x G) -> z `in` dom G \/ z = y).
Proof. induction G; intros; eauto. destruct a. simpl in *.
       apply add_iff in H. inversion H; clear H.
       - unfold rename_atom in H0.
         destruct (a == x). subst. auto.
         subst. auto.
       - move: (IHG x y z H0) => h. inversion h; auto.
Qed.

Lemma rename_context_co_tmdom : forall G x y,
      (forall z, In z (tmdom (rename_context_co y x G)) ->
                                  In z (tmdom G) \/ z = y).
Proof. induction G; intros; eauto. destruct a. destruct s; simpl in *; eauto.
       inversion H; clear H.
       - unfold rename_atom in H0.
         destruct (a == x). apply singleton_iff in H0. subst. auto.
         apply singleton_iff in H0. subst. auto. auto.
       - move: (IHG x y z H0) => h. inversion h; auto.
Qed.

Lemma list_rename_context_co_dom : forall l G,
      (forall x, x `in` dom (list_rename_context_co l G) ->
                      x `in` dom G \/ In x (left_list l)).
Proof. induction l; eauto.
       intros. destruct a. simpl in *.
       move: (IHl (rename_context_co a a0 G) x H) => h.
       inversion h; clear h. apply rename_context_co_dom in H0.
       inversion H0; auto. auto.
Qed.

Lemma list_rename_context_co_tmdom : forall l G,
      (forall x, In x (tmdom (list_rename_context_co l G)) ->
                      In x (tmdom G) \/ In x (left_list l)).
Proof. induction l; eauto.
       intros. destruct a. simpl in *.
       move: (IHl (rename_context_co a a0 G) x H) => h.
       inversion h; clear h. apply rename_context_co_tmdom in H0.
       inversion H0; auto. auto.
Qed.

(* ------------------------------------------------------------- *)

(* Lemmas on commutativity of two rename operations for tms, sorts, contexts *)

Lemma subst_commute_tm_co : forall A x1 x2 y1 y2,
      x2 <> x1 -> x2 <> y1 -> y2 <> x1 ->
      co_subst_co_tm (g_Var_f y2) x2 (co_subst_co_tm (g_Var_f y1) x1 A) =
      co_subst_co_tm (g_Var_f y1) x1 (co_subst_co_tm (g_Var_f y2) x2 A).
Proof. intros. rewrite co_subst_co_tm_co_subst_co_tm; eauto.
       rewrite co_subst_co_co_fresh_eq. simpl; auto. auto.
Qed.

Lemma subst_commute_sort_co : forall s x1 x2 y1 y2,
      x2 <> x1 -> x2 <> y1 -> y2 <> x1 ->
      co_subst_co_sort (g_Var_f y2) x2 (co_subst_co_sort (g_Var_f y1) x1 s) =
      co_subst_co_sort (g_Var_f y1) x1 (co_subst_co_sort (g_Var_f y2) x2 s).
Proof. intros. destruct s; simpl; f_equal.
       apply subst_commute_tm_co; auto.
       rewrite co_subst_co_constraint_co_subst_co_constraint; eauto.
       rewrite co_subst_co_co_fresh_eq. simpl; auto. auto.
Qed.

Lemma rename_context_commute_co :  forall G x1 y1 x2 y2,
      x2 <> x1 -> x2 <> y1 -> y2 <> x1 ->
      rename_context_co y1 x1 (rename_context_co y2 x2 G) =
      rename_context_co y2 x2 (rename_context_co y1 x1 G).
Proof. induction G; intros; eauto. destruct a. simpl in *.
       f_equal. rewrite rename_atom_commute; eauto.
       rewrite subst_commute_sort_co; eauto. eauto.
Qed.

(* ------------------------------------------------------------- *)

(* Lemmas on commutativity of list-renaming and a single rename on tms
   and contexts *)

Lemma list_rename_rename_commute_co : forall l x y b,
      ~In x (left_list l) -> ~In x (right_list l) -> ~In y (right_list l) ->
      list_rename_co l (co_subst_co_tm (g_Var_f y) x b) =
      co_subst_co_tm (g_Var_f y) x (list_rename_co l b).
Proof. induction l; intros; eauto.
       destruct a; simpl in *. rewrite subst_commute_tm_co.
       simpl; eauto. simpl; eauto. eauto. eapply IHl; eauto.
Qed.

Lemma list_rename_rename_commute_context_co : forall l x y G,
      ~In x (left_list l) -> ~In x (right_list l) -> ~In y (right_list l) ->
      list_rename_context_co l (rename_context_co y x G) =
      rename_context_co y x (list_rename_context_co l G).
Proof. induction l; intros; eauto. destruct a. simpl in *.
       rewrite rename_context_commute_co; eauto. eapply IHl; eauto.
Qed.

(* ----------------------------------------------------------- *)

(** Main covars renaming lemma **)

Lemma list_co_rename_typing :
    forall l G, NoDup (left_list l) -> NoDup (right_list l) ->
                disj_list_list (left_list l) (right_list l) ->
                disj_list_set (left_list l) (dom G) ->
                disj_list_list (right_list l) (tmdom G) ->
    (forall b B (H : Typing G b B),
        Typing (list_rename_context_co l G)
               (list_rename_co l b)
               (list_rename_co l B)).
Proof. induction l; intros; eauto.
       destruct a; simpl in *.
       unfold disj_list_list in *. unfold disj_list_set in *.
       rewrite list_rename_rename_commute_co. intro. apply (H1 a0).
       simpl; auto. simpl; auto. inversion H0; subst; auto.
       intro. apply (H1 a). simpl; auto. simpl; auto.
       rewrite list_rename_rename_commute_co. intro. apply (H1 a0).
       simpl; auto. simpl; auto. inversion H0; subst; auto.
       intro. apply (H1 a). simpl; auto. simpl; auto.
       rewrite list_rename_rename_commute_context_co.
       intro. apply (H1 a0). simpl; auto. simpl; auto.
       inversion H0; subst; auto. intro. apply (H1 a). simpl; auto. simpl; auto.
       eapply co_rename_mutual. eapply IHl.
       inversion H; subst; eauto. inversion H0; subst; eauto.
       intros. intro. apply (H1 x). simpl; auto. simpl; auto.
       intros. intro. apply (H2 x). simpl; auto. auto.
       intros. intro. apply (H3 x). simpl; auto. auto. auto.
       intro. apply list_rename_context_co_dom in H5. inversion H5; clear H5.
       apply (H2 a). simpl; auto. auto. inversion H; subst; auto.
       intro. apply list_rename_context_co_tmdom in H5. inversion H5; clear H5.
       apply (H3 a0). simpl; auto. auto. apply (H1 a0). simpl; auto. simpl; auto.
Qed.

(** --------------------------------------------------------------
    --------------------------------------------------------------
 **)

Definition list_rename_role_context l W :=
  fold_left (fun W' yx => rename_role_context yx.1 yx.2 W') l W.

Lemma list_rename_atom_app : forall V a1 a2 l,
      List.map (list_rename_atom ((a1, a2) :: l)) V =
      List.map (list_rename_atom l) (List.map (rename_atom a1 a2) V).
Proof. induction V; intros. auto.
       simpl. f_equal. eauto.
Qed.

(** PatternContexts list version **)

Lemma list_tm_rename_PatternContexts: forall l W G V F A p B,
       NoDup (left_list l) -> NoDup (right_list l) ->
       disj_list_list (left_list l) (right_list l) ->
       disj_list_set (left_list l) (dom G) ->
       disj_list_list (right_list l) (codom G) ->
      PatternContexts W G V F A p B ->
      PatternContexts (list_rename_role_context l W)
      (list_rename_context_tm l G) (List.map (list_rename_atom l) V)
      F (list_rename_tm l A) (list_rename_tm l p) (list_rename_tm l B).
Proof. induction l; intros; simpl in *.
       unfold list_rename_atom. simpl. eauto.
       clear - H4. induction H4; eauto. simpl. econstructor. auto. eauto.
       destruct a. simpl. rewrite list_rename_atom_app. eapply IHl.
       inversion H; auto. inversion H0; auto. unfold disj_list_list in *.
       intros. intro. apply (H1 x). simpl; auto. simpl; auto.
       unfold disj_list_set in *.
       intros. intro. apply rename_context_tm_dom in H6.
       inversion H6; clear H6. apply (H2 x). simpl; auto. auto.
       subst. inversion H; auto.
       unfold disj_list_list in *.
       intros. intro. apply rename_context_tm_codom in H6.
       inversion H6; clear H6. apply (H3 x). simpl; auto. auto.
       subst. apply (H1 a). simpl; auto. simpl; auto.
       eapply PatternContexts_rename_tm. auto. unfold disj_list_set in *.
       intro. apply (H2 a). simpl; auto. auto. intro.
       unfold disj_list_list in *. apply (H3 a0). simpl; auto. auto.
Qed.

Lemma list_co_rename_PatternContexts: forall l W G V F A p B,
       NoDup (left_list l) -> NoDup (right_list l) ->
       disj_list_list (left_list l) (right_list l) ->
       disj_list_set (left_list l) (dom G) ->
       disj_list_list (right_list l) (tmdom G) ->
      PatternContexts W G V F A p B ->
      PatternContexts (list_rename_role_context l W)
      (list_rename_context_co l G) (List.map (list_rename_atom l) V)
      F (list_rename_co l A) (list_rename_co l p) (list_rename_co l B).
Proof. induction l; intros; simpl in *.
       unfold list_rename_atom. simpl. eauto.
       clear - H4. induction H4; eauto. simpl. econstructor. auto. eauto.
       destruct a. simpl. rewrite list_rename_atom_app. eapply IHl.
       inversion H; auto. inversion H0; auto. unfold disj_list_list in *.
       intros. intro. apply (H1 x). simpl; auto. simpl; auto.
       unfold disj_list_set in *.
       intros. intro. apply rename_context_co_dom in H6.
       inversion H6; clear H6. apply (H2 x). simpl; auto. auto.
       subst. inversion H; auto.
       unfold disj_list_list in *.
       intros. intro. apply rename_context_co_tmdom in H6.
       inversion H6; clear H6. apply (H3 x). simpl; auto. auto.
       subst. apply (H1 a). simpl; auto. simpl; auto.
       eapply PatternContexts_rename_co. auto. unfold disj_list_set in *.
       intro. apply (H2 a). simpl; auto. auto. intro.
       unfold disj_list_list in *. apply (H3 a0). simpl; auto. auto.
Qed.

(** -----------------------------------------------------
    -----------------------------------------------------
 **)

Lemma codom_dom : forall G x, In x (codom G) -> x `in` dom G.
Proof. induction G; intros; simpl in *; eauto.
       contradiction. destruct a. destruct s; simpl in *; eauto.
       inversion H; eauto.
Qed.

Lemma tmdom_dom : forall G x, In x (tmdom G) -> x `in` dom G.
Proof. induction G; intros; simpl in *; eauto.
       contradiction. destruct a. destruct s; simpl in *; eauto.
       inversion H; eauto.
Qed.

Lemma tm_subst_same : forall l A,
     (forall x, In x (right_list l) -> x `notin` fv_tm_tm_tm A) ->
     list_rename_tm l A = A.
Proof. induction l; intros. eauto.
       destruct a. simpl. rewrite tm_subst_tm_tm_fresh_eq.
       eapply H. simpl; auto. eapply IHl. intros. eapply H.
       simpl; auto.
Qed.

Lemma co_subst_same : forall l A,
     (forall x, In x (right_list l) -> x `notin` fv_co_co_tm A) ->
     list_rename_co l A = A.
Proof. induction l; intros. eauto.
       destruct a. simpl. rewrite co_subst_co_tm_fresh_eq.
       eapply H. simpl; auto. eapply IHl. intros. eapply H.
       simpl; auto.
Qed.

Fixpoint var_var_pairs (px py : tm) : list (var * var) :=
   match (px,py) with
 | (a_Fam F, a_Fam F') => []
 | (a_App p1 (Role R) (a_Var_f y), a_App p2 (Role R') (a_Var_f x)) =>
                                       var_var_pairs p1 p2 ++ [(y,x)]
 | (a_App p1 (Rho Irrel) a_Bullet, a_App p2 (Rho Irrel) a_Bullet) =>
                                       var_var_pairs p1 p2
 | (a_CApp p1 g_Triv, a_CApp p2 g_Triv) => var_var_pairs p1 p2
 | (_,_) => []
   end.

Lemma left_list_app : forall A B (l1 : list (A * B)) l2,
      left_list (l1 ++ l2) = left_list l1 ++ left_list l2.
Proof. induction l1; intros; eauto.
       destruct a. simpl. f_equal. eauto.
Qed.

Lemma right_list_app : forall A B (l1 : list (A * B)) l2,
      right_list (l1 ++ l2) = right_list l1 ++ right_list l2.
Proof. induction l1; intros; eauto.
       destruct a. simpl. f_equal. eauto.
Qed.

Lemma var_var_pairs_vars_pattern_left : forall p1 p2 b1 b2 D1 D2,
      Rename p1 b1 p2 b2 D1 D2 ->
      left_list (var_var_pairs p2 p1) = vars_Pattern p2.
Proof. intros. induction H; simpl; eauto.
       rewrite left_list_app. simpl. f_equal. eauto.
Qed.

Lemma var_var_pairs_vars_pattern_right : forall p1 p2 b1 b2 D1 D2,
      Rename p1 b1 p2 b2 D1 D2 ->
      right_list (var_var_pairs p2 p1) = vars_Pattern p1.
Proof. intros. induction H; simpl; eauto.
       rewrite right_list_app. simpl. f_equal. eauto.
Qed.

Fixpoint list_to_pattern (F : const) (l : list atom) :=
  match l with
  | nil => a_Fam F
  | x :: l' => a_App (list_to_pattern F l') (Role Nom) (a_Var_f x)
  end.

Lemma list_to_pattern_Pattern : forall F l, Pattern (list_to_pattern F l).
Proof. induction l; simpl; eauto.
Qed.

Lemma var_tmvar_covar : forall G x, x `in` dom G -> In x (tmdom G) \/
                                                    In x (codom G).
Proof. induction G; intros. simpl in *. left; fsetdec.
       destruct a. destruct s; simpl in *. apply add_iff in H.
       inversion H. eauto. move: (IHG x H0) => h. inversion h; eauto.
       apply add_iff in H. inversion H. eauto.
       move: (IHG x H0) => h. inversion h; eauto.
Qed.

Lemma PatternContexts_tmvars : forall W G D F A p B x,
      PatternContexts W G D F A p B -> In x (tmdom G) ->
      x `in` fv_tm_tm_tm p \/ In x D.
Proof. intros. induction H; simpl in *; eauto.
       inversion H0; clear H0. subst. left. clear. fsetdec.
       move: (IHPatternContexts H2) => h. inversion h; eauto.
       inversion H0. subst. auto.
       move: (IHPatternContexts H2) => h. inversion h; eauto.
       move: (IHPatternContexts H0) => h. inversion h; eauto.
Qed.

Lemma rename_context_tmdom_tm : forall l G,
      tmdom (list_rename_context_tm l G) =
      List.map (list_rename_atom l) (tmdom G).
Proof. induction l; intros; simpl in *.
       unfold list_rename_atom. simpl.
       induction G; eauto. destruct a. destruct s; simpl in *; eauto.
       f_equal; auto.
       destruct a. simpl. rewrite IHl. clear.
       induction G. unfold list_rename_atom. simpl. auto.
       destruct a1. destruct s. simpl. f_equal. auto.
       simpl. auto.
Qed.

Lemma rename_context_codom_co : forall l G,
      codom (list_rename_context_co l G) =
      List.map (list_rename_atom l) (codom G).
Proof. induction l; intros; simpl in *.
       unfold list_rename_atom. simpl.
       induction G; eauto. destruct a. destruct s; simpl in *; eauto.
       f_equal; auto.
       destruct a. simpl. rewrite IHl. clear.
       induction G. unfold list_rename_atom. simpl. auto.
       destruct a1. destruct s. simpl. auto. simpl. f_equal. auto.
Qed.

Lemma rename_context_tmdom_co : forall l G,
      tmdom (list_rename_context_co l G) =
      List.map (list_rename_atom l) (tmdom G).
Proof. induction l; intros; simpl in *.
       unfold list_rename_atom. simpl.
       induction G; eauto. destruct a. destruct s; simpl in *; eauto.
       f_equal; auto.
       destruct a. simpl. rewrite IHl. clear.
       induction G. unfold list_rename_atom. simpl. auto.
       destruct a1. destruct s. simpl. f_equal. auto.
       simpl. auto.
Qed.

Lemma rename_context_codom_tm : forall l G,
      codom (list_rename_context_tm l G) =
      List.map (list_rename_atom l) (codom G).
Proof. induction l; intros; simpl in *.
       unfold list_rename_atom. simpl.
       induction G; eauto. destruct a. destruct s; simpl in *; eauto.
       f_equal; auto.
       destruct a. simpl. rewrite IHl. clear.
       induction G. unfold list_rename_atom. simpl. auto.
       destruct a1. destruct s. simpl. auto. simpl. f_equal. auto.
Qed.

Lemma list_rename_context_tm_nil : forall l, list_rename_context_tm l nil = nil.
Proof. induction l; eauto.
Qed.

Lemma rename_context_tm_app : forall G1 G2 y x,
      rename_context_tm y x (G1 ++ G2) =
                     rename_context_tm y x G1 ++ rename_context_tm y x G2.
Proof. induction G1; intros; eauto.
       simpl. destruct a. simpl. f_equal. eauto.
Qed.

Lemma list_rename_context_tm_app : forall l G1 G2,
      list_rename_context_tm l (G1 ++ G2) = list_rename_context_tm l G1
         ++ list_rename_context_tm l G2.
Proof. induction l. intros. unfold list_rename_context_tm. simpl.
       auto. intros. destruct G1.
       simpl. rewrite list_rename_context_tm_nil. simpl. auto.
       simpl. destruct a. simpl. destruct p. simpl.
       rewrite cons_app_one. rewrite IHl. rewrite cons_app_one.
       rewrite IHl. rewrite <- app_assoc. f_equal.
       rewrite rename_context_tm_app. eauto.
Qed.

Lemma list_rename_context_tm_split : forall l G,
      left_list (list_rename_context_tm l G) =
      List.map (list_rename_atom l) (left_list G).
Proof. induction l; intros; simpl in *.
       unfold list_rename_atom. simpl.
       induction G; eauto. destruct a. destruct s; simpl in *; eauto.
       f_equal; auto. f_equal; auto.
       destruct a. simpl. rewrite IHl. clear.
       induction G. unfold list_rename_atom. simpl. auto.
       destruct a1. destruct s. simpl. f_equal. auto.
       simpl. f_equal; auto.
Qed.

Lemma tmdom_app : forall G1 G2, tmdom (G1 ++ G2) = tmdom G1 ++ tmdom G2.
Proof. induction G1; intros; eauto.
       destruct a. destruct s. simpl. f_equal. eauto.
       simpl. eauto.
Qed.

Lemma list_rename_atom_same : forall l a, ~In a (right_list l) ->
      list_rename_atom l a = a.
Proof. induction l; intros; eauto. destruct a. simpl in *.
       destruct (a0 == a1). subst. assert False. apply H. auto.
       contradiction. rewrite rename_atom_diff_same. auto. eauto.
Qed.

Lemma list_rename_atom_list_same : forall l' l,
      (forall x, In x l' -> ~In x (right_list l)) ->
      List.map (list_rename_atom l) l' = l'.
Proof. induction l'; intros; eauto. simpl.
       rewrite list_rename_atom_same. intro. apply (H a).
       simpl; auto. auto. f_equal. eapply IHl'.
       intros. intro. apply (H x). simpl; auto. auto.
Qed.

Lemma list_rename_atom_inll : forall l a, In a (right_list l) ->
      disj_list_list (left_list l) (right_list l) ->
      In (list_rename_atom l a) (left_list l).
Proof. induction l; intros; eauto.
       simpl. destruct a. simpl in *.
       inversion H; clear H. subst. rewrite rename_atom_diff.
       left. rewrite list_rename_atom_same.
       unfold disj_list_list in *. intro. eapply (H0 a). simpl; auto.
       simpl; auto. auto. destruct (a0 == a1). subst.
       rewrite rename_atom_diff. rewrite list_rename_atom_same.
       unfold disj_list_list in *. intro. eapply (H0 a). simpl; auto.
       simpl; auto. auto. right. rewrite rename_atom_diff_same.
       auto. eapply IHl. auto. unfold disj_list_list in *. intros.
       intro. apply (H0 x). simpl; auto. simpl; auto.
Qed.

Lemma list_rename_atom_nil : forall l, List.map (list_rename_atom l) nil = nil.
Proof. induction l; eauto.
Qed.

Lemma list_rename_atom_list_inll : forall l' l,
      disj_list_list (left_list l) (right_list l) ->
      (forall x, In x l' -> In x (right_list l)) ->
      (forall y, In y (List.map (list_rename_atom l) l') -> In y (left_list l)).
Proof. induction l'; intros; eauto. rewrite list_rename_atom_nil in H1.
       simpl in H1. contradiction.
       simpl in *. inversion H1. subst. eapply list_rename_atom_inll.
       eapply (H0 a). auto. auto. eauto.
Qed.

Lemma codom_app : forall G1 G2, codom (G1 ++ G2) = codom G1 ++ codom G2.
Proof. induction G1; intros; eauto.
       destruct a. destruct s. simpl. eauto. simpl. f_equal. eauto.
Qed.

Lemma list_rename_context_co_nil : forall l, list_rename_context_co l nil = nil.
Proof. induction l; eauto.
Qed.

Lemma rename_context_co_app : forall G1 G2 y x,
      rename_context_co y x (G1 ++ G2) =
                     rename_context_co y x G1 ++ rename_context_co y x G2.
Proof. induction G1; intros; eauto.
       simpl. destruct a. simpl. f_equal. eauto.
Qed.

Lemma list_rename_context_co_app : forall l G1 G2,
      list_rename_context_co l (G1 ++ G2) = list_rename_context_co l G1
         ++ list_rename_context_co l G2.
Proof. induction l. intros. unfold list_rename_context_co. simpl.
       auto. intros. destruct G1.
       simpl. rewrite list_rename_context_co_nil. simpl. auto.
       simpl. destruct a. simpl. destruct p. simpl.
       rewrite cons_app_one. rewrite IHl. rewrite cons_app_one.
       rewrite IHl. rewrite <- app_assoc. f_equal.
       rewrite rename_context_co_app. eauto.
Qed.

Lemma chainsubst_list_rename_tm : forall p p' b b1 b2 D D',
       Rename p b1 p' b2 D D' ->
       chain_subst p' p b = list_rename_tm (var_var_pairs p' p) b.
Proof. intros. generalize dependent b. induction H; intros; simpl; eauto.
       unfold chain_subst in *. simpl. unfold list_rename_tm in *.
       rewrite fold_left_app. rewrite fold_left_app. simpl.
       f_equal. eauto.
Qed.

Lemma vars_Pattern_list_to_pattern : forall F V,
      vars_Pattern (list_to_pattern F V) = rev V.
Proof. intros. induction V; eauto. simpl. f_equal. auto.
Qed.

Lemma PatternContexts_irrvar : forall W G D F A p B,
      PatternContexts W G D F A p B -> (forall x, In x D -> x `in` dom G).
Proof. intros. induction H; simpl in *; eauto. contradiction.
       inversion H0. subst. eauto. eauto.
Qed.

Lemma PatternContexts_irrvar_tmdom : forall W G D F A p B,
      PatternContexts W G D F A p B -> (forall x, In x D -> In x (tmdom G)).
Proof. intros. induction H; simpl in *; eauto.
       inversion H0. subst. eauto. eauto.
Qed.

Lemma Rename_imp_var : forall p b p1 b1 D D1 x, Rename p b p1 b1 D D1 ->
       x `in` D -> x `in` fv_tm_tm_tm p1 -> False.
Proof. intros. assert (x `notin` D1).
         eapply Rename_inter_empty. eauto. eauto.
         apply H2. eapply AtomSetProperties.in_subset.
         eauto. eapply Rename_fv_new_pattern. eauto.
Qed.

Lemma PatternContexts_pattern_fv_dom : forall W G D F A p B x,
      PatternContexts W G D F A p B -> x `in` fv_tm_tm_tm p ->
      x `in` dom G.
Proof. intros. induction H; simpl in *; eauto.
       apply union_iff in H0. inversion H0. eauto. eauto.
       apply union_iff in H0. inversion H0. eauto. fsetdec.
       apply union_iff in H0. inversion H0. eauto. fsetdec.
Qed.

Lemma PatternContexts_pattern_fv_tmdom : forall W G D F A p B x,
      PatternContexts W G D F A p B -> x `in` fv_tm_tm_tm p ->
      In x (tmdom G).
Proof. intros. induction H; simpl in *; eauto. fsetdec.
       apply union_iff in H0. inversion H0. eauto. eauto.
       apply union_iff in H0. inversion H0. eauto. fsetdec.
       apply union_iff in H0. inversion H0. eauto. fsetdec.
Qed.

Lemma PatternContexts_tmdom_vars : forall W G D F A p B x,
      PatternContexts W G D F A p B -> In x (tmdom G) <->
      In x (vars_Pattern p) \/ In x (rev D).
Proof. intros. induction H; simpl in *; split; intros; eauto.
       inversion H0; contradiction.
       inversion H1; clear H1. subst. left. apply in_or_app. simpl. eauto.
       move: (IHPatternContexts.1 H2) => h. inversion h.
       left. apply in_or_app. eauto. right. auto.
       inversion H1; clear H1. apply in_app_or in H2.
       inversion H2; clear H2. right. eapply IHPatternContexts.2. auto.
       inversion H1; subst; eauto. simpl in H2. contradiction.
       right. eapply IHPatternContexts.2. auto.
       inversion H1; clear H0. subst. right. apply in_or_app. simpl. eauto.
       move: (IHPatternContexts.1 H2) => h. inversion h.
       left. auto. right. apply in_or_app; auto.
       inversion H1; clear H1. right. eapply IHPatternContexts.2. auto.
       apply in_app_or in H2. inversion H2; clear H2.
       right. eapply IHPatternContexts.2. auto.
       inversion H1; subst; eauto. simpl in H2. contradiction.
       eapply IHPatternContexts.1. auto. eapply IHPatternContexts.2. auto.
Qed.

Lemma PatternContexts_NoDup : forall W G V F A p B,
      PatternContexts W G V F A p B -> NoDup (tmdom G) ->
      NoDup (vars_Pattern p) /\ NoDup V.
Proof. intros. induction H; simpl in *; eauto.
       split. rewrite <- rev_involutive. apply NoDup_reverse.
       rewrite rev_app_distr. simpl. apply NoDup_cons.
       intro. apply in_rev in H2. inversion H0; subst.
       apply H5. eapply PatternContexts_tmdom_vars. eauto. auto.
       apply NoDup_reverse. inversion H0; subst.
       apply IHPatternContexts in H5. inversion H5; auto. 
       inversion H0; subst.
       apply IHPatternContexts in H5. inversion H5; auto. split.
       inversion H0; subst.
       apply IHPatternContexts in H5. inversion H5; auto.
        inversion H0; subst. econstructor. intro.
        apply H4. eapply PatternContexts_tmdom_vars. eauto. right.
        apply in_rev in H2. auto.
        apply IHPatternContexts in H5. inversion H5; auto.
Qed.

Lemma PatternContexts_pattern_irrvar_disj : forall W G V F A p B,
      PatternContexts W G V F A p B -> NoDup (tmdom G) ->
      (forall x, x `in` fv_tm_tm_tm p -> ~ In x V).
Proof. intros. induction H; simpl in *; eauto.
       - apply union_iff in H1. inversion H1. inversion H0; subst.
         eauto.
         intro. apply PatternContexts_irrvar_tmdom with (x := x) in H.
         apply singleton_iff in H3. subst. inversion H0; subst.
         contradiction. auto.
       - intro. inversion H3. subst.
         apply PatternContexts_pattern_fv_tmdom with (x := x) in H.
         inversion H0; subst. contradiction. fsetdec.
         inversion H0; subst. apply IHPatternContexts; auto. fsetdec.
       - apply IHPatternContexts; auto. fsetdec.
Qed.

Lemma Context_tmdom_codom_contr : forall G x, Ctx G -> In x (tmdom G) ->
      In x (codom G) -> False.
Proof. intros. induction H; simpl in *. contradiction.
       inversion H0; clear H0. apply H3. apply codom_dom. subst. auto.
       eauto. inversion H1; clear H1. apply H3. apply tmdom_dom. subst. auto.
       eauto.
Qed.

Lemma Context_tmdom_codom_NoDup : forall G, Ctx G -> NoDup (tmdom G) /\
      NoDup (codom G).
Proof. intros. induction H; simpl in *; split.
       eapply NoDup_nil. eapply NoDup_nil.
       eapply NoDup_cons. intro. apply H1. apply tmdom_dom. auto.
       all: try (inversion IHCtx; auto).
       eapply NoDup_cons. intro. apply H1. apply codom_dom. auto. auto.
Qed.

Lemma NoDup_app : forall l1 l2, NoDup l1 -> NoDup l2 ->
      disj_list_list l1 l2 -> NoDup (l1 ++ l2).
Proof. induction l1; intros; eauto. simpl.
       eapply NoDup_cons. intro. apply in_app_or in H2.
       inversion H2; clear H2. inversion H; subst; auto.
       unfold disj_list_list in H1. apply (H1 a). simpl; auto. auto.
       eapply IHl1. inversion H; auto. auto.
       unfold disj_list_list in *. intros. intro. apply (H1 x).
       simpl; auto. auto.
Qed.

Lemma Rename_Pattern : forall p b p' b' D D', Rename p b p' b' D D' -> Pattern p'.
Proof. intros. induction H; auto.
Qed.

Lemma Pattern_fv_co_co_tm_empty : forall p, Pattern p -> fv_co_co_tm p [<=] empty.
Proof. intros. induction H; simpl; fsetdec.
Qed.

Lemma matchsubst_app : forall a p nu a1 a2, tm_pattern_agree a p ->
           matchsubst a p (a_App a1 nu a2) =
           a_App (matchsubst a p a1) nu (matchsubst a p a2).
Proof. intros. induction H; simpl; auto. rewrite IHtm_pattern_agree.
       simpl. auto.
Qed.

Lemma matchsubst_capp : forall a p a1, tm_pattern_agree a p ->
      matchsubst a p (a_CApp a1 g_Triv) = a_CApp (matchsubst a p a1) g_Triv.
Proof. intros. induction H; simpl; auto. rewrite IHtm_pattern_agree.
       simpl. auto.
Qed.

Lemma matchsubst_fv : forall a p b, tm_pattern_agree a p -> lc_tm b ->
      fv_tm_tm_tm (matchsubst a p b) [<=]
     ((AtomSetImpl.diff (fv_tm_tm_tm b) (fv_tm_tm_tm p)) \u fv_tm_tm_tm a).
Proof. intros. apply MatchSubst_fv. apply matchsubst_fun_ind; auto.
Qed.

Lemma Rename_lc_1 : forall p p' b b' D D', Rename p b p' b' D D' -> lc_tm p.
Proof. intros. induction H; auto.
Qed.

Lemma Rename_matchsubst_pattern : forall p p' b b' D D',
      Rename p b p' b' D D' -> uniq_atoms_pattern p ->
      fv_tm_tm_tm p [<=] D -> p' = matchsubst p' p p.
Proof. intros. induction H; simpl; eauto.
       - simpl in H1.
         unfold uniq_atoms_pattern in *.
         simpl in H0. apply NoDup_reverse in H0. rewrite rev_app_distr in H0.
         simpl in H0. inversion H0; subst.
         apply NoDup_reverse in H6. rewrite rev_involutive in H6.
         rewrite matchsubst_app.  eapply Rename_tm_pattern_agree.
         eauto. simpl. f_equal. rewrite tm_subst_tm_tm_fresh_eq.
         rewrite matchsubst_fv. rewrite AtomSetProperties.diff_subset_equal.
         apply notin_union_3. clear; fsetdec.
         intro. eapply Rename_inter_empty with (x := x). eauto.
         fsetdec. move: (Rename_fv_new_pattern H) => h. fsetdec.
         auto. eapply Rename_tm_pattern_agree. eauto.
         eapply Rename_lc_1. eauto. eauto.
         rewrite matchsubst_chain_subst.
         eapply Rename_tm_pattern_agree. eauto.
         erewrite chainsubst_list_rename_tm.
         rewrite tm_subst_same. erewrite var_var_pairs_vars_pattern_right.
         intros. simpl. intro. apply singleton_iff in H4. subst.
         apply H5. apply in_rev. rewrite rev_involutive. auto. eauto.
         simpl. destruct (x == x); [|contradiction]. auto. eauto.
       - simpl in H1.
         unfold uniq_atoms_pattern in *.
         simpl in H0. rewrite matchsubst_app.
         eapply Rename_tm_pattern_agree. eauto. f_equal. eauto.
         symmetry. apply matchsubst_ind_fun.
         apply tm_pattern_agree_bullet_bullet.
         eapply Rename_tm_pattern_agree. eauto.
       - simpl in H1.
         unfold uniq_atoms_pattern in *.
         simpl in H0. rewrite matchsubst_capp.
         eapply Rename_tm_pattern_agree. eauto. f_equal. eauto.
Qed.

Lemma Rename_chainsubst_pattern : forall p p' b b' D D',
      Rename p b p' b' D D' -> uniq_atoms_pattern p ->
      fv_tm_tm_tm p [<=] D -> p' = chain_subst p' p p.
Proof. intros. eapply transitivity. eapply Rename_matchsubst_pattern; eauto.
       eapply matchsubst_chain_subst. eapply Rename_tm_pattern_agree. eauto.
Qed.

Lemma Ctx_NoDup : forall G, Ctx G -> NoDup (tmdom G).
Proof. intros. induction H; simpl; eauto.
       econstructor. econstructor. intro. apply tmdom_dom in H2.
       contradiction. auto.
Qed.

Lemma Rename_new_body_fv_new_pattern : forall p b p' b' D D',
      Rename p b p' b' D D' -> fv_tm_tm_tm b [<=] fv_tm_tm_tm p ->
      fv_tm_tm_tm b' [<=] fv_tm_tm_tm p'.
Proof. intros. eapply Subset_trans. eapply Rename_fv_body. eauto.
       fsetdec.
Qed.

Lemma axiom_fresh : forall s (G0 : list (atom * s))
      p b p1 b1 D1 D1' D2 W G V F A B a b'',
      fv_tm_tm_tm A [<=] empty /\ fv_co_co_tm A [<=] empty /\
      fv_tm_tm_tm b [<=] fv_tm_tm_tm p /\
      uniq_atoms_pattern p /\
      union (fv_tm_tm_tm a) (union (fv_tm_tm_tm p) (fv_tm_tm_tm b)) [<=] D1 ->
      Rename p b p1 b1 D1 D1' /\
      PatternContexts W G V F A p B /\
      Typing G b B -> MatchSubst a p1 b1 b'' ->
      exists p2 b2 D2' W' G' V' B',
      Rename p b p2 b2 D2 D2' /\ MatchSubst a p2 b2 b'' /\
      PatternContexts W' G' V' F A p2 B' /\
      Typing G' b2 B' /\ disjoint G' G0 /\
      (forall x, In x V' -> x `notin` fv_tm_tm_tm b2).
Proof. intros. rename H1 into Q. inversion H0 as [h1 [h2 h3]]; clear H0.
       move: (patctx_pattern h2) => h4.
       move: (Typing_lc1 h3) => h5.
       move: (Rename_exists (dom G0 \u dom G \u (fv_tm_tm_tm p) \u (fv_tm_tm_tm a \u D2)) h4 h5) => h6.
       inversion h6 as [p' [b' [D2' h7]]].
       remember (var_var_pairs p' p) as l1.
       move: (list_to_pattern_Pattern F V) => h8.
       move: (Rename_exists (dom G0 \u dom G \u D2 \u D2') h8 lc_a_Bullet) => h9.
       inversion h9 as [px [bx [Dx hx]]].
       remember (var_var_pairs px (list_to_pattern F V)) as l2.
       move: (list_to_pattern_Pattern F (codom G)) => h10.
       move: (Rename_exists (dom G0 \u dom G \u D2 \u D2' \u Dx) h10 lc_a_Bullet) => h11.
       inversion h11 as [py [bz [Dy hy]]].
       remember (var_var_pairs py (list_to_pattern F (codom G))) as l3.
       remember (list_rename_co l3 (list_rename_tm l2 (list_rename_tm l1 p))) as p2.
       remember (list_rename_co l3 (list_rename_tm l2 (list_rename_tm l1 b))) as b2.
       remember (list_rename_co l3 (list_rename_tm l2 (list_rename_tm l1 B))) as B'.
       remember (list_rename_co l3 (list_rename_tm l2 (list_rename_tm l1 A))) as A'.
       assert (A = A'). clear Heql1 Heql2 Heql3.
       subst. rewrite (tm_subst_same l1). intros. intro. clear - H1 H.
       inversion H. fsetdec. rewrite tm_subst_same. intros. intro. clear - H1 H.
       inversion H. fsetdec. rewrite co_subst_same. intros. intro. clear - H1 H.
       inversion H. fsetdec. auto.
       remember (list_rename_context_co l3
                  (list_rename_context_tm (l1 ++ l2) G)) as G'.
       remember (list_rename_role_context l3 
             (list_rename_role_context (l1 ++ l2) W)) as W'.
       remember (List.map (list_rename_atom l3)
           (List.map (list_rename_atom (l1 ++ l2)) V)) as V'.
       exists p2, b2, D2', W', G', V', B'.
       assert (P1 : NoDup (left_list l3)).
        { subst. erewrite var_var_pairs_vars_pattern_left.
          eapply uniq_atoms_new_pattern. eauto. eauto. }
       assert (P2 : NoDup (right_list l3)).
        { subst. erewrite var_var_pairs_vars_pattern_right.
          rewrite vars_Pattern_list_to_pattern. apply NoDup_reverse.
          apply Context_tmdom_codom_NoDup. eapply Typing_Ctx. eauto.
          eauto. } 
       assert (P3 : disj_list_list (left_list l3) (right_list l3)).
         { subst. erewrite var_var_pairs_vars_pattern_right.
          rewrite vars_Pattern_list_to_pattern.
           erewrite var_var_pairs_vars_pattern_left.
           unfold disj_list_list. intros. intro.
           apply vars_pattern_fv in H1. apply in_rev in H2.
           apply codom_dom in H2. clear - H1 H2 hy.
           eapply Rename_imp_var; eauto. eauto. eauto.
         }
       assert (P3' : disj_list_list
       (left_list (var_var_pairs p' p ++ var_var_pairs px (list_to_pattern F V)))
       (right_list (var_var_pairs p' p ++ var_var_pairs px (list_to_pattern F V)))).
         {   rewrite left_list_app. rewrite right_list_app.
             erewrite var_var_pairs_vars_pattern_left.
             erewrite var_var_pairs_vars_pattern_left.
             erewrite var_var_pairs_vars_pattern_right.
             erewrite var_var_pairs_vars_pattern_right.
             rewrite vars_Pattern_list_to_pattern. 
             unfold disj_list_list. intros. intro.
             rename H2 into H4. rename H1 into H2.
             apply in_app_or in H2. apply in_app_or in H4.
             inversion H2 as [H5 | H5]; inversion H4 as [H6 | H6]; clear H2 H4.
             apply vars_pattern_fv in H5. apply vars_pattern_fv in H6.
             move: (PatternContexts_pattern_fv_dom h2 H6) => k21.
             clear - H5 k21 h7. eapply Rename_imp_var; eauto.
             apply in_rev in H6. apply vars_pattern_fv in H5.
             move: (PatternContexts_irrvar h2 x H6) => k21.
             clear - H5 k21 h7. eapply Rename_imp_var; eauto.
             apply vars_pattern_fv in H6. apply vars_pattern_fv in H5.
             move: (PatternContexts_pattern_fv_dom h2 H6) => k21.
             clear - H5 k21 hx. eapply Rename_imp_var; eauto. 
             apply in_rev in H6. apply vars_pattern_fv in H5.
             move: (PatternContexts_irrvar h2 x H6) => k21.
             clear - H5 k21 hx. eapply Rename_imp_var; eauto.
             eauto. eauto. eauto. eauto.
             }
       assert (P3'' : disj_list_set
       (left_list (var_var_pairs p' p ++ var_var_pairs px (list_to_pattern F V)))
       (dom G)).
       { unfold disj_list_set. intros. intro.
         rewrite left_list_app in H1.
         erewrite var_var_pairs_vars_pattern_left in H1.
         erewrite var_var_pairs_vars_pattern_left in H1.
         apply in_app_or in H1.
          inversion H1; clear H1.
           apply vars_pattern_fv in H3. clear - H2 H3 h7.
           eapply Rename_imp_var; eauto.
           apply vars_pattern_fv in H3. clear - H2 H3 hx.
           eapply Rename_imp_var; eauto. eauto. eauto. }

       assert (P4 : disj_list_set (left_list l3) 
                    (dom (list_rename_context_tm (l1 ++ l2) G))).
         { subst. erewrite var_var_pairs_vars_pattern_left.
           unfold disj_list_set. intros. intro.
           apply var_tmvar_covar in H2. inversion H2; clear H2.
           - rewrite rename_context_tmdom_tm in H3.
             apply list_rename_atom_list_inll in H3.
             rewrite left_list_app in H3.
             erewrite var_var_pairs_vars_pattern_left in H3.
             erewrite var_var_pairs_vars_pattern_left in H3.
             apply in_app_or in H3. inversion H3; clear H3.
             eapply Rename_imp_var. eapply hy.
             eapply AtomSetProperties.in_subset.
             eapply vars_pattern_fv. eapply H2. 
             eapply Subset_trans. eapply Rename_fv_new_pattern. eauto.
             clear. fsetdec. eapply vars_pattern_fv. eauto.
             eapply Rename_imp_var. eapply hy.
             eapply AtomSetProperties.in_subset.
             eapply vars_pattern_fv. eapply H2. 
             eapply Subset_trans. eapply Rename_fv_new_pattern. eauto.
             clear. fsetdec. eapply vars_pattern_fv. eauto. eauto.
             eauto. auto.
             intros. rewrite right_list_app.
             erewrite var_var_pairs_vars_pattern_right.
             erewrite var_var_pairs_vars_pattern_right.
             rewrite vars_Pattern_list_to_pattern.
             apply in_or_app. eapply PatternContexts_tmdom_vars.
             eauto. auto. eauto. eauto.
           - rewrite rename_context_codom_tm in H3.
             rewrite list_rename_atom_list_same in H3.
             intros. intro. rewrite right_list_app in H3.
             erewrite var_var_pairs_vars_pattern_right in H3.
             erewrite var_var_pairs_vars_pattern_right in H3.
             rewrite vars_Pattern_list_to_pattern in H3.
             apply in_app_or in H3. eapply Context_tmdom_codom_contr.
             eapply Typing_Ctx. eauto. eapply PatternContexts_tmdom_vars.
             eauto. eauto. auto. eauto. eauto.
             apply codom_dom in H3. apply vars_pattern_fv in H1.
             clear - H1 H3 hy. eapply Rename_imp_var; eauto.
           - eauto.
           }
         assert (P5 : disj_list_list (right_list l3) 
                    (tmdom (list_rename_context_tm (l1 ++ l2) G))).
         { rewrite rename_context_tmdom_tm.
           unfold disj_list_list. intros. intro.
           subst. erewrite var_var_pairs_vars_pattern_right in H1.
           rewrite vars_Pattern_list_to_pattern in H1.
           apply in_rev in H1.
           apply list_rename_atom_list_inll in H2.
           rewrite left_list_app in H2.
           erewrite var_var_pairs_vars_pattern_left in H2.
           erewrite var_var_pairs_vars_pattern_left in H2.
           apply in_app_or in H2. apply codom_dom in H1. inversion H2; clear H2.
           apply vars_pattern_fv in H3. clear - H1 H3 h7.
           eapply Rename_imp_var; eauto.
           apply vars_pattern_fv in H3. clear - H1 H3 hx.
           eapply Rename_imp_var; eauto. eauto. eauto. auto.
             intros. rewrite right_list_app.
             erewrite var_var_pairs_vars_pattern_right.
             erewrite var_var_pairs_vars_pattern_right.
             rewrite vars_Pattern_list_to_pattern.
             apply in_or_app. eapply PatternContexts_tmdom_vars.
             eauto. auto. eauto. eauto. eauto. }

      assert (P6 : disj_list_list
     (right_list (var_var_pairs p' p ++ var_var_pairs px (list_to_pattern F V)))
     (codom G)).
         { unfold disj_list_list. intros. intro. rewrite right_list_app in H1.
           erewrite var_var_pairs_vars_pattern_right in H1.
           erewrite var_var_pairs_vars_pattern_right in H1.
           rewrite vars_Pattern_list_to_pattern in H1.
           apply in_app_or in H1. eapply Context_tmdom_codom_contr.
           eapply Typing_Ctx. eauto. eapply PatternContexts_tmdom_vars.
           eauto. eauto. auto. eauto. eauto. }

    assert (P7 : NoDup (left_list (l1 ++ l2))).
    { subst. rewrite left_list_app.
      erewrite var_var_pairs_vars_pattern_left.
      erewrite var_var_pairs_vars_pattern_left.
      apply NoDup_app. eapply uniq_atoms_new_pattern. eauto.
      eapply uniq_atoms_new_pattern. eauto.
      unfold disj_list_list. intros. intro.
      apply vars_pattern_fv in H1. apply vars_pattern_fv in H2.
      eapply Rename_imp_var. eapply hx.
      eapply AtomSetProperties.in_subset.
      eapply H1. eapply Subset_trans. eapply Rename_fv_new_pattern. eauto.
      clear. fsetdec. eauto. eauto. eauto. }

    assert (P8 : NoDup (right_list (l1 ++ l2))).
   { subst. rewrite right_list_app.
     erewrite var_var_pairs_vars_pattern_right.
     erewrite var_var_pairs_vars_pattern_right.
     rewrite vars_Pattern_list_to_pattern.
     assert (NoDup (tmdom G)). { eapply Context_tmdom_codom_NoDup.
     eapply Typing_Ctx. eauto. }
     pose (K := PatternContexts_NoDup h2 H1). inversion K.
     apply NoDup_app. auto. apply NoDup_reverse. auto.
     unfold disj_list_list. intros. intro.
     apply vars_pattern_fv in H4. apply in_rev in H5.
     eapply PatternContexts_pattern_irrvar_disj; eauto.
     eapply hx. eauto. }
     assert (Q1 : p2 = p').
       { rewrite Heqp2. rewrite Heql1.
         erewrite <- chainsubst_list_rename_tm.
         erewrite <- Rename_chainsubst_pattern.
         rewrite (tm_subst_same l2).
         intros. rewrite Heql2 in H1.
         erewrite var_var_pairs_vars_pattern_right in H1.
         rewrite vars_Pattern_list_to_pattern in H1.
         apply in_rev in H1.
         eapply PatternContexts_irrvar with (G := G) in H1. intro.
         eapply Rename_imp_var with (x := x). eapply h7. auto.
         eauto. eauto. eauto. rewrite co_subst_same. intros.
         rewrite Pattern_fv_co_co_tm_empty. fsetdec.
         eapply Rename_Pattern. eapply h7. auto.
         eapply h7. split_hyp; auto. clear. fsetdec. eauto.
       }
    assert (Q2 : b2 = b').
         { assert (Q21 : list_rename_tm l1 b = b').
               { subst. erewrite <- chainsubst_list_rename_tm.
                 erewrite Rename_chain_subst. eauto. eauto. eauto.
               }
          assert (S1 : fv_tm_tm_tm b [<=] fv_tm_tm_tm p).
          split_hyp; auto.
          move: (Rename_new_body_fv h7 S1) => k1.
          rewrite Heqb2. rewrite Q21. rewrite (tm_subst_same l2).
          intros. rewrite Heql2 in H1.
          erewrite var_var_pairs_vars_pattern_right in H1.
          rewrite vars_Pattern_list_to_pattern in H1.
          apply in_rev in H1.
          eapply PatternContexts_irrvar with (G := G) in H1.
          eapply subset_notin. eapply Rename_inter_empty.
          eapply h7. eauto. eapply Rename_new_body_fv. eapply h7.
          split_hyp; auto. eauto. eauto.
          rewrite co_subst_same. intros.
          erewrite Rename_new_body_fv_co. eauto. eapply h7.
          eapply Typing_context_fv in h3. split_hyp; auto.
          auto.
        }
         assert (Q' : PatternContexts W' G' V' F A p2 B').
        {
         subst. rewrite H0. eapply list_co_rename_PatternContexts.
         all: auto.
         unfold list_rename_tm. rewrite <- fold_left_app.
         rewrite <- fold_left_app. rewrite <- fold_left_app.
         eapply list_tm_rename_PatternContexts.
         subst. all:auto.
        }
         assert (Q'' : Typing G' b2 B').
       {
         subst.
         eapply list_co_rename_typing. all: auto.
         unfold list_rename_tm. rewrite <- fold_left_app.
         rewrite <- fold_left_app.
         eapply list_tm_rename_typing.
         all: auto.
        }
        repeat split.
       -  rewrite Q1. rewrite Q2. eapply Rename_narrow. eauto. clear. fsetdec.
       - assert (Q3 : MatchSubst a p2 b2 (matchsubst a p2 b2)).
         { apply matchsubst_fun_ind. rewrite Q1.
           eapply tm_pattern_agree_rename_inv_1.
           eapply tm_pattern_agree_rename_inv_2. eapply MatchSubst_match.
           eauto. eauto. eauto. rewrite Q2. eapply Rename_lc4. eauto.
           auto.
         }
         replace b'' with (matchsubst a p2 b2). auto.
         symmetry. eapply MatchSubst_Rename_preserve.
         eapply tm_pattern_agree_rename_inv_2.
         eapply MatchSubst_match. eapply Q. eapply h1. eapply h1.
         eapply h7. split_hyp; auto. eapply Typing_context_fv in h3.
         inversion h3 as [Hyp _]. clear - Hyp. fsetdec.
         split_hyp; auto. auto. rewrite <- Q1. rewrite <- Q2. auto.
       - auto.
       - auto.
       - clear Q''. intro. intros.
         apply inter_iff in H1. inversion H1; clear H1.
         subst. apply var_tmvar_covar in H2. inversion H2; clear H2.
         + rewrite rename_context_tmdom_co in H1.
           rewrite list_rename_atom_list_same in H1.
           * intros. intro. erewrite var_var_pairs_vars_pattern_right in H2.
             rewrite vars_Pattern_list_to_pattern in H2.
             apply in_rev in H2.
             rewrite rename_context_tmdom_tm in H1.
             apply list_rename_atom_list_inll in H1.
             rewrite left_list_app in H1.
             erewrite var_var_pairs_vars_pattern_left in H1.
             erewrite var_var_pairs_vars_pattern_left in H1.
             apply in_app_or in H1. 
             inversion H1; clear H1. apply codom_dom in H2.
             apply vars_pattern_fv in H4. clear - H2 H4 h7.
             eapply Rename_imp_var; eauto.
              apply codom_dom in H2.
             apply vars_pattern_fv in H4. clear - H2 H4 hx.
             eapply Rename_imp_var; eauto. eauto. eauto.
             unfold disj_list_list. intros. intro.
             rewrite left_list_app in H4. rewrite right_list_app in H5.
             erewrite var_var_pairs_vars_pattern_left in H4.
             erewrite var_var_pairs_vars_pattern_left in H4.
             erewrite var_var_pairs_vars_pattern_right in H5.
             erewrite var_var_pairs_vars_pattern_right in H5.
             rewrite vars_Pattern_list_to_pattern in H5.
             apply in_app_or in H4. apply in_app_or in H5.
             inversion H4; inversion H5.
             apply vars_pattern_fv in H6. apply vars_pattern_fv in H7.
             move: (PatternContexts_pattern_fv_dom h2 H7) => k21.
             clear - H6 k21 h7. eapply Rename_imp_var; eauto.
             apply in_rev in H7. apply vars_pattern_fv in H6.
             move: (PatternContexts_irrvar h2 x0 H7) => k21.
             clear - H6 k21 h7. eapply Rename_imp_var; eauto.
             apply vars_pattern_fv in H6. apply vars_pattern_fv in H7.
             move: (PatternContexts_pattern_fv_dom h2 H7) => k21.
             clear - H6 k21 hx. eapply Rename_imp_var; eauto. 
             apply in_rev in H7. apply vars_pattern_fv in H6.
             move: (PatternContexts_irrvar h2 x0 H7) => k21.
             clear - H6 k21 hx. eapply Rename_imp_var; eauto.
             eauto. eauto. eauto. eauto.
             intros. rewrite right_list_app.
             erewrite var_var_pairs_vars_pattern_right.
             erewrite var_var_pairs_vars_pattern_right.
             rewrite vars_Pattern_list_to_pattern.
             apply in_or_app. eapply PatternContexts_tmdom_vars.
             eauto. auto. eauto. eauto. eauto.
           * rewrite rename_context_tmdom_tm in H1.
             apply list_rename_atom_list_inll in H1.
             ** rewrite left_list_app in H1.
                erewrite var_var_pairs_vars_pattern_left in H1.
                erewrite var_var_pairs_vars_pattern_left in H1.
                apply in_app_or in H1. inversion H1; clear H1.
                apply vars_pattern_fv in H2.
                clear - H3 H2 h7. assert False. eapply Rename_imp_var; eauto.
                contradiction.
                apply vars_pattern_fv in H2.
                clear - H3 H2 hx. assert False. eapply Rename_imp_var; eauto.
                contradiction.
                eauto. eauto.
             ** rewrite left_list_app. rewrite right_list_app.
                erewrite var_var_pairs_vars_pattern_left.
                erewrite var_var_pairs_vars_pattern_left.
                erewrite var_var_pairs_vars_pattern_right.
                erewrite var_var_pairs_vars_pattern_right.
                unfold disj_list_list. intros. intro.
                apply in_app_or in H2. apply in_app_or in H4.
                inversion H2; inversion H4.
                apply vars_pattern_fv in H5. apply vars_pattern_fv in H6.
                move: (PatternContexts_pattern_fv_dom h2 H6) => k21.
                clear - H5 k21 h7. eapply Rename_imp_var; eauto.
                apply vars_pattern_fv in H5.
                rewrite vars_Pattern_list_to_pattern in H6.
                apply in_rev in H6. move: (PatternContexts_irrvar h2) => k3.
                apply k3 in H6. clear - H5 H6 h7.
                eapply Rename_imp_var; eauto.
                apply vars_pattern_fv in H5. apply vars_pattern_fv in H6.
                 move: (PatternContexts_pattern_fv_dom h2 H6) => k21.
                clear - H5 k21 hx. eapply Rename_imp_var; eauto.
                apply vars_pattern_fv in H5.
                rewrite vars_Pattern_list_to_pattern in H6.
                apply in_rev in H6. move: (PatternContexts_irrvar h2) => k3.
                apply k3 in H6. clear - H5 H6 hx. eapply Rename_imp_var; eauto.
                eauto. eauto. eauto. eauto.
             ** intros. rewrite right_list_app.
                erewrite var_var_pairs_vars_pattern_right.
                erewrite var_var_pairs_vars_pattern_right.
                rewrite vars_Pattern_list_to_pattern.
                apply in_or_app.
                eapply PatternContexts_tmdom_vars; eauto. eauto. eauto.
         + rewrite rename_context_codom_co in H1.
           rewrite rename_context_codom_tm in H1.
           rewrite (list_rename_atom_list_same (codom G)) in H1.
            * intros. intro. rewrite right_list_app in H2.
              erewrite var_var_pairs_vars_pattern_right in H2.
              erewrite var_var_pairs_vars_pattern_right in H2.
              rewrite vars_Pattern_list_to_pattern in H2.
              apply in_app_or in H2. eapply Context_tmdom_codom_contr.
              eapply Typing_Ctx. eauto. eapply PatternContexts_tmdom_vars.
              eauto. eauto. auto. eauto. eauto.
            * apply list_rename_atom_list_inll in H1.
              erewrite var_var_pairs_vars_pattern_left in H1.
              apply vars_pattern_fv in H1. clear - H1 H3 hy.
              assert False. eapply Rename_imp_var; eauto.
              contradiction. eauto.
              erewrite var_var_pairs_vars_pattern_left.
              erewrite var_var_pairs_vars_pattern_right.
              rewrite vars_Pattern_list_to_pattern.
              unfold disj_list_list. intros. intro.
              apply vars_pattern_fv in H2. apply in_rev in H4.
              apply codom_dom in H4. clear - H2 H4 hy.
              eapply Rename_imp_var; eauto. eauto. eauto.
              intros. erewrite var_var_pairs_vars_pattern_right.
              rewrite vars_Pattern_list_to_pattern.
              apply in_rev. rewrite rev_involutive. auto. eauto.
        - intros. intro. eapply PatternContexts_pattern_irrvar_disj.
          eapply Q'. apply Ctx_NoDup. eapply Typing_Ctx. eauto.
          eapply Superset_cont_sub. eapply Rename_new_body_fv_new_pattern.
          rewrite <- Q1 in h7. eauto. split_hyp; auto. rewrite <- Q2.
          eauto. auto.
Qed.