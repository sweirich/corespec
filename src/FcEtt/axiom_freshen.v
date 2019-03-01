
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
        - eapply E_Case. eauto. eauto. eauto. admit. eauto. auto.
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
        - eapply E_PatCong. eauto. eauto. eauto. admit. admit. all:eauto.
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
Admitted.

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
        - eapply E_Case. eauto. eauto. eauto. admit. eauto. auto.
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
        - eapply E_PatCong. eauto. eauto. eauto. admit. admit. all:eauto.
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
Admitted.

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

Lemma rename_context_tmdom : forall l G,
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

Lemma rename_context_codom : forall l G,
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

Lemma list_rename_atom_inll : forall l a, In a (right_list l) ->
      NoDup (right_list l) ->
      disj_list_list (left_list l) (right_list l) ->
      In (list_rename_atom l a) (left_list l).
Proof. induction l; intros; eauto.
       simpl. destruct a. simpl in *.
       inversion H; clear H. subst. rewrite rename_atom_diff.
       left. rewrite list_rename_atom_same.
       unfold disj_list_list in *. intro. eapply (H1 a). simpl; auto.
       simpl; auto. auto. destruct (a0 == a1). subst.
       rewrite rename_atom_diff. right. Admitted.

Lemma tmdom_renamed_context : forall G l,
      NoDup (right_list l) ->
      NoDup (left_list l) ->
      disj_list_list (left_list l) (right_list l) ->
      (forall x, In x (tmdom G) -> In x (right_list l)) ->
      (forall y, In y (tmdom (list_rename_context_tm l G))
                                  -> In y (left_list l)).
Proof. induction G; intros; simpl in *.
       rewrite list_rename_context_tm_nil in H3. simpl in H3. contradiction.
       destruct a. rewrite cons_app_one in H3.
       rewrite list_rename_context_tm_app in H3.
       rewrite tmdom_app in H3. apply in_app_or in H3.
       inversion H3. destruct s.
       assert (y = list_rename_atom l a). admit. subst.
        simpl in *.
        eapply IHG; eauto.
       intros.   Admitted.

Lemma axiom_fresh : forall p b p1 b1 D1 D1' D2 W G V F A B,
      fv_tm_tm_tm A [<=] empty /\ fv_co_co_tm A [<=] empty ->
      Rename p b p1 b1 D1 D1' /\
      PatternContexts W G V F A p B /\
      Typing G b B ->
      exists p2 b2 D2' W' G' V' B',
      Rename p b p2 b2 D2 D2' /\
      PatternContexts W' G' V' F A p2 B' /\
      Typing G' b2 B' /\ disjoint G' G.
Proof. intros. inversion H0 as [h1 [h2 h3]]; clear H0.
       move: (patctx_pattern h2) => h4.
       move: (Typing_lc1 h3) => h5.
       move: (Rename_exists D2 h4 h5) => h6.
       inversion h6 as [p' [b' [D2' h7]]].
       remember (var_var_pairs p' p) as l1.
       move: (list_to_pattern_Pattern F V) => h8.
       move: (Rename_exists (D2 \u D2') h8 lc_a_Bullet) => h9.
       inversion h9 as [px [bx [Dx hx]]].
       remember (var_var_pairs px (list_to_pattern F V)) as l2.
       move: (list_to_pattern_Pattern F (codom G)) => h10.
       move: (Rename_exists (D2 \u D2' \u Dx) h10 lc_a_Bullet) => h11.
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
       (*assert (P1 : NoDup (left_list l3)).
       assert (P2 : NoDup (right_list l3)).
       assert (P3 : disjoint_list_set (left_list l3)
                    (dom (list_rename_context_tm (l1 ++ l2) G))).
       assert (P4 : disjoint_list_list (right_list *)         
       repeat split.
       - clear Heql1 Heql2 Heql3. assert (Q1 : p2 = p'). admit.
         rewrite Q1.
         assert (Q2 : b2 = b'). admit. rewrite Q2. auto.
       - clear Heql1 Heql2 Heql3.
         subst. rewrite H0. eapply list_co_rename_PatternContexts.
         admit. admit. admit. admit. admit.
         unfold list_rename_tm. rewrite <- fold_left_app.
         rewrite <- fold_left_app. rewrite <- fold_left_app.
         eapply list_tm_rename_PatternContexts.
         admit. admit. admit. admit. admit. auto.
       - clear Heql1 Heql2 Heql3. subst.
         eapply list_co_rename_typing.
         admit. admit. admit. admit. admit.
         unfold list_rename_tm. rewrite <- fold_left_app.
         rewrite <- fold_left_app.
         eapply list_tm_rename_typing.
         admit. admit. admit. admit. admit. auto.
       - intro. intros. Admitted.
(*
Definition atom_pairs_rename (G : context) (D : atoms) :=
  let tmvars := tmdom G in
  let (atom_pairs_tmvar, new_tmvars) := atoms_excl tmvars (dom G \u D) in
  let covars := codom G in
  let (atom_pairs_covar, _) := atoms_excl covars (D \u new_tmvars) in
  (atom_pairs_tmvar,atom_pairs_covar).

Definition rename_entire_context (G : context) (D : atoms) :=
  let (atom_pairs_tmvar,atom_pairs_covar) := atom_pairs_rename G D in
  list_rename_context_tm atom_pairs_tmvar
      (list_rename_context_co atom_pairs_covar G).


Lemma renamed_context_disj : forall G D, disjoint G (rename_entire_context G D).
Proof. induction G; intros. simpl; eauto.
       intro. intros. apply inter_iff in H. inversion H;clear H.
       unfold rename_entire_context in *.



Definition 



Inductive var : Set :=
  | var_tmvar : atom -> var
  | var_covar : atom -> var.

Fixpoint context_vars (G : context) :=
   match G with
    | nil => nil
    | (x, Tm _) :: G' => var_tmvar x :: context_vars G'
    | (c, Co _) :: G' => var_covar c :: context_vars G'
   end.

Fixpoint open_tm_wrt_var (a : tm) (v : var) :=
   match v with
   | var_tmvar x => open_tm_wrt_tm a (a_Var_f x)
   | var_covar c => open_tm_wrt_co a (g_Var_f c)
   end.

Fixpoint close_tm_wrt_var (a : tm) (v : var) :=
   match v with
   | var_tmvar x => close_tm_wrt_tm x a
   | var_covar c => close_tm_wrt_co c a
   end.

Definition close_tm_wrt_context (G : context) (b : tm) :=
   fold_left close_tm_wrt_var (context_vars G) b.

Definition open_tm_wrt_context (G : context) (b : tm) :=
   fold_left open_tm_wrt_var (context_vars G) b.

Fixpoint close_tm_wrt_context_list (G : context) (bs : list tm) :=
  match G with
  | nil => bs
  | (x, Tm _) :: G' =>
    match bs with
      | nil => nil
      | b :: _ => close_tm_wrt_context_list G' (close_tm_wrt_tm x b :: bs)
    end
  | (c, Co _) :: G' =>
     match bs with
      | nil => nil
      | b :: _ => close_tm_wrt_context_list G' (close_tm_wrt_co c b :: bs)
     end
  end.

Fixpoint open_tm_wrt_context_list (G : context) (bs : list tm) :=
  match G with
  | nil => bs
  | (x, Tm _) :: G' =>
     match bs with
     | nil => nil
     | b :: _ => open_tm_wrt_context_list G' (open_tm_wrt_tm b (a_Var_f x) :: bs)
     end
  | (c, Co _) :: G' =>
     match bs with
     | nil => nil
     | b :: _ => open_tm_wrt_context_list G' (open_tm_wrt_co b (g_Var_f c) :: bs)
     end
  end.

Inductive tmco : Set :=
  | tmco_tm : tm -> tmco
  | tmco_co : co -> tmco.

Fixpoint open_tm_wrt_tmcos_list (l : list tmco) (bs : list tm) :=
  match l with
  | nil => bs
  | tmco_tm a :: l' =>
    match bs with
    | nil => nil
    | b :: _ => open_tm_wrt_tmcos_list l' (open_tm_wrt_tm b a :: bs)
    end
  | tmco_co g :: l' =>
    match bs with
    | nil => nil
    | b :: _ => open_tm_wrt_tmcos_list l' (open_tm_wrt_co b g :: bs)
    end
  end.

Fixpoint tm_tmcos (a : tm) : list tmco :=
  match a with
  | a_Fam F => nil
  | a_App a1 nu a2 => tm_tmcos a1 ++ [ tmco_tm a2 ]
  | a_CApp a1 g => tm_tmcos a1 ++ [ tmco_co g ]
  | _ => nil
  end.

Fixpoint tm_init_segs (a : tm) (l : list tm) :=
  match a with
  | a_Fam F => a_Fam F :: l
  | a_App a1 _ _ => tm_init_segs a1 (a :: l)
  | a_CApp a1 _ => tm_init_segs a1 (a :: l)
  | _ => l
  end.

Inductive tm_open_tm_type (G : context) : tm -> tm -> Prop :=
 | tm_open_tm_type_base : forall F p b A R1 Rs,
    binds F (Ax p b A R1 Rs) toplevel -> Ctx G -> tm_open_tm_type G (a_Fam F) A
 | tm_open_tm_type_appR : forall a A' A a' R,
    tm_open_tm_type G a (a_Pi Rel A' A) -> Typing G a' A' ->
    tm_open_tm_type G (a_App a (Role R) a') (open_tm_wrt_tm A a')
 | tm_open_tm_type_appIrrel : forall a A' A a',
    tm_open_tm_type G a (a_Pi Irrel A' A) -> Typing G a' A' ->
    tm_open_tm_type G (a_App a (Rho Irrel) a_Bullet) (open_tm_wrt_tm A a')
 | tm_open_tm_type_capp : forall a a' b' T' R A,
    tm_open_tm_type G a (a_CPi (Eq a' b' T' R) A) ->
    DefEq G (dom G) a' b' T' R ->
    tm_open_tm_type G (a_CApp a g_Triv) (open_tm_wrt_co A g_Triv).

Inductive initial_seg : tm -> tm -> Prop :=
 | initial_seg_base : forall F, initial_seg (a_Fam F) (a_Fam F)
 | initial_seg_app : forall a1 nu a2 a, initial_seg a a1 ->
                     initial_seg a (a_App a1 nu a2)
 | initial_seg_capp : forall a1 g a, initial_seg a a1 ->
                     initial_seg a (a_CApp a1 g).

initial_seg a' a -> tm_open_tm_type G a' A' -> Typing G a' A'.

Lemma close_open_same : forall G b,
      open_tm_wrt_context G (close_tm_wrt_context G b) = b.


Definition chain_subst_sort a p b := fold_left
       (fun b' a'x' => tm_subst_tm_sort a'x'.1 a'x'.2 b') (tm_var_pairs a p) b.


Lemma matchsubst_typing : forall W G1 G2 F A p' B' W' p B b' b a G G',
   PatternContexts W G' F A p' B' -> Typing G' b' B' ->
   PatternContexts W' G2 F A p B -> G' = G1 ++ G2 -> Typing G2 b B -> tm_pattern_agree a p ->
   Typing G a (matchsubst a p B) ->
   Typing ((map (chain_subst_sort a p) G1) ++ G)
                                  (matchsubst a p b') (matchsubst a p B').
Proof. intros. generalize dependent a. generalize dependent b.
       generalize dependent G1.
       induction H1; intros.
        - inversion H4; subst. simpl in *. admit.
        - inversion H5; subst. inversion H6; subst.
          simpl matchsubst.
          replace
           (map (chain_subst_sort (a_App a1 (Role R) a2)
                                  (a_App p (Role R) (a_Var_f x))) G1
                                    ++ G) with
   (map (tm_subst_tm_sort a2 x) (map (chain_subst_sort a1 p) G1) ++ G).
          eapply tm_substitution_mutual. eapply IHPatternContexts. auto.
          rewrite app_assoc. eauto.
          rewrite fold_left_app.
*)
