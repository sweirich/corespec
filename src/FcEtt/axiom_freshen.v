
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

Definition rename_atom (a b c : atom) : atom := if c == b then a else c.

Fixpoint codom (G : context) :=
   match G with
    | nil => empty
    | (x, Tm _) :: G' => codom G'
    | (c, Co _) :: G' => singleton c \u codom G'
   end.

Fixpoint tmdom (G : context) :=
   match G with
    | nil => empty
    | (x, Tm _) :: G' => singleton x \u tmdom G'
    | (c, Co _) :: G' => tmdom G'
   end.

Lemma binds_codom : forall G c phi, binds c (Co phi) G -> c `in` codom G.
Proof. intro G. induction G; intros; eauto. inversion H.
       destruct a. destruct s; inversion H; simpl. inversion H0. eauto.
       inversion H0; eauto. eauto.
Qed.

Lemma binds_tmdom : forall G x A, binds x (Tm A) G -> x `in` tmdom G.
Proof. intro G. induction G; intros; eauto. inversion H.
       destruct a. destruct s; inversion H; simpl. inversion H0. eauto.
       eauto. inversion H0. eauto.
Qed.

Definition rename_context_tm (a b : atom) G :=
 List.map 
  (fun zA => (rename_atom a b zA.1, tm_subst_tm_sort (a_Var_f a) b zA.2)) G.

Definition rename_context_co (a b : atom) G :=
 List.map 
  (fun zA => (rename_atom a b zA.1, co_subst_co_sort g_Triv b zA.2)) G.

Definition rename_role_context (a b : atom) (W : role_context) :=
 List.map (fun zR => (rename_atom a b zR.1, zR.2)) W.

Definition rename_atoms (a b : atom) D :=
  if (AtomSetImpl.mem b D) then singleton a \u (remove b D) else D.

Lemma rename_context_tm_app :
      forall G1 G2 x y, rename_context_tm y x (G1 ++ G2) =
                        rename_context_tm y x G1 ++ rename_context_tm y x G2.
Proof. intros G1. induction G1; intros; eauto. simpl. f_equal. eauto.
Qed.

Lemma rename_atom_same : forall y a, rename_atom y y a = a.
Proof. intros. unfold rename_atom. destruct (a == y); auto.
Qed.

Lemma rename_atom_diff : forall y a, rename_atom y a a = y.
Proof. intros. unfold rename_atom. destruct (a == a); auto. contradiction.
Qed.

Lemma rename_atom_diff_same : forall x y a, a <> x -> rename_atom y x a = a.
Proof. intros. unfold rename_atom. destruct (a == x); auto. contradiction.
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

Lemma tm_subst_tm_same_mutual : forall y,
      (forall b, tm_subst_tm_tm (a_Var_f y) y b = b) /\
      (forall brs, tm_subst_tm_brs (a_Var_f y) y brs = brs) /\
      (forall g, tm_subst_tm_co (a_Var_f y) y g = g) /\
      (forall phi, tm_subst_tm_constraint (a_Var_f y) y phi = phi).
Proof. intros. apply tm_brs_co_constraint_mutind; intros; simpl; f_equal; eauto.
       destruct (x == y); subst; auto.
Qed.

Lemma tm_subst_tm_sort_same : forall y s, tm_subst_tm_sort (a_Var_f y) y s = s.
Proof. intros. destruct s; simpl; f_equal; eapply (tm_subst_tm_same_mutual y).
Qed.

Lemma rename_context_tm_same : forall y G,
      rename_context_tm y y G = G.
Proof. intros. induction G; eauto.
       destruct a. simpl. rewrite rename_atom_same.
       rewrite tm_subst_tm_sort_same. f_equal; auto.
Qed.

Lemma rename_binds_tm : forall G x x0 y s, binds x s G ->
      binds (rename_atom y x0 x) (tm_subst_tm_sort (a_Var_f y) x0 s)
                                              (rename_context_tm y x0 G).
Proof. intro G. induction G; intros; eauto.
       inversion H; subst. simpl. unfold rename_atom.
       destruct (x == x0); eauto. simpl. eauto.
Qed.

Lemma rename_binds_co : forall G x x0 y s, binds x s G ->
      binds (rename_atom y x0 x) (co_subst_co_sort g_Triv x0 s)
                                 (rename_context_co y x0 G).
Proof. intro G. induction G; intros; eauto.
       inversion H; subst. simpl. unfold rename_atom.
       destruct (x == x0); eauto. simpl. eauto.
Qed.

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

Lemma remove_in_same : forall s x, remove x s [=] remove x (singleton x \u s).
Proof. intros. fsetdec.
Qed.
(*
Lemma PatternContexts_irrvar_cong : forall W G D1 D2 F A p B,
      PatternContexts W G D1 F A p B -> D1 [=] D2 ->
      PatternContexts W G D2 F A p B.
Proof. intros. generalize dependent D2. induction H; intros; eauto.
       admit. move: (AtomSetProperties.In_dec x D) => h.
       inversion h. 

Lemma PatternContexts_rename : forall W G D F p A B x y,
      PatternContexts W G D F A p B -> y `notin` dom G -> x `notin` codom G ->
      PatternContexts (rename_role_context y x W) (rename_context_tm y x G)
       (rename_atoms y x D) F (tm_subst_tm_tm (a_Var_f y) x A)
       (tm_subst_tm_tm (a_Var_f y) x p) (tm_subst_tm_tm (a_Var_f y) x B).
Proof. intros. induction H.
        - simpl in *. unfold rename_atoms.
          destruct (AtomSetImpl.mem x empty) eqn:h.
          apply AtomSetImpl.mem_2 in h. fsetdec. eauto with lngen lc.
        - destruct (x0 == x). subst. rewrite tm_subst_tm_tm_open_tm_wrt_tm.
          eauto. rewrite tm_subst_tm_tm_same_diff.
          rewrite tm_subst_tm_tm_app_same_diff. 
          simpl. unfold rename_atom. destruct (x == x); [|contradiction].
          eapply PatCtx_PiRel with (L := remove y L).
          eauto. eauto. rewrite tm_subst_tm_tm_open_tm_wrt_tm.
          eauto. rewrite tm_subst_tm_tm_diff. auto.
          rewrite tm_subst_tm_tm_app_diff. auto.
          simpl. unfold rename_atom. destruct (x0 == x); [contradiction|].
          eapply PatCtx_PiRel with (L := remove x0 L).
          eauto. eauto.
        - destruct (x0 == x). subst. rewrite tm_subst_tm_tm_open_tm_wrt_tm.
          eauto. rewrite tm_subst_tm_tm_same_diff.
          simpl. unfold rename_atom. destruct (x == x); [|contradiction].
          unfold rename_atoms in *.
          destruct (AtomSetImpl.mem x (union (singleton x) D)) eqn:h.
          destruct (AtomSetImpl.mem x D) eqn:h'.
          replace (singleton y \u (remove x (singleton x \u D)))
          with (singleton y \u singleton y \u (remove x (singleton x \u D))).
          eapply PatCtx_PiIrr with (L := remove y L).
          replace (remove x (singleton x \u D)) with (remove x D).
          eauto. intro. apply remove_in_same. clear. simpl in *.
          move: (AtomSetProperties.In_dec x D) => h1.
          inversion h1. earch "dec" "`in`".
          eauto. eauto. rewrite tm_subst_tm_tm_open_tm_wrt_tm.
          eauto. rewrite tm_subst_tm_tm_diff. auto.
          rewrite tm_subst_tm_tm_app_diff. auto.
          simpl. unfold rename_atom. destruct (x0 == x); [contradiction|].
          eapply PatCtx_PiRel with (L := remove x0 L).
          eauto. eauto.  
*)
Lemma tm_rename_mutual :
   (forall G b B (H : Typing G b B),
      forall x y, y `notin` dom G -> x `notin` codom G ->
        Typing (rename_context_tm y x G)
               (tm_subst_tm_tm (a_Var_f y) x b)
               (tm_subst_tm_tm (a_Var_f y) x B)) /\
    (forall G phi  (H : PropWff G phi),
       forall x y, y `notin` dom G -> x `notin` codom G ->
        PropWff (rename_context_tm y x G)
                (tm_subst_tm_constraint (a_Var_f y) x phi) ) /\
    (forall G D p1 p2  (H : Iso G D p1 p2 ),
       forall x y, y `notin` dom G -> x `notin` codom G ->
        Iso (rename_context_tm y x G) D
            (tm_subst_tm_constraint (a_Var_f y) x p1)
            (tm_subst_tm_constraint (a_Var_f y) x p2) ) /\
    (forall G D A B T R (H : DefEq G D A B T R),
       forall x y, y `notin` dom G -> x `notin` codom G ->
         DefEq (rename_context_tm y x G) D
               (tm_subst_tm_tm (a_Var_f y) x A) (tm_subst_tm_tm (a_Var_f y) x B)
               (tm_subst_tm_tm (a_Var_f y) x T) R) /\
    (forall G (H : Ctx G),
        forall x y, y `notin` dom G -> x `notin` codom G ->
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
          simpl; auto. apply h; auto.
        - eapply E_CAbs with (L := singleton y \u singleton x \u L); eauto.
          intros. move: (H c ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite tm_subst_tm_tm_open_tm_wrt_co in h. eauto.
          rewrite (tm_subst_tm_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. rewrite tm_subst_tm_tm_open_tm_wrt_co in h. eauto.
          rewrite (tm_subst_tm_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. apply h; auto.
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
        - eapply E_CAbsCong with (L := singleton y \u singleton x \u L).
          intros. move: (H c ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite tm_subst_tm_tm_open_tm_wrt_co in h. eauto.
          rewrite (tm_subst_tm_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. rewrite tm_subst_tm_tm_open_tm_wrt_co in h. eauto.
          rewrite (tm_subst_tm_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. rewrite tm_subst_tm_tm_open_tm_wrt_co in h. eauto.
          rewrite (tm_subst_tm_co_fresh_eq (g_Var_f c)) in h.
          simpl; auto. apply h; auto. eauto.
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
      forall x y, y `notin` dom G -> x `notin` tmdom G ->
        Typing (rename_context_co y x G)
               (co_subst_co_tm g_Triv x b)
               (co_subst_co_tm g_Triv x B)) /\
    (forall G phi  (H : PropWff G phi),
       forall x y, y `notin` dom G -> x `notin` tmdom G ->
        PropWff (rename_context_co y x G)
                (co_subst_co_constraint g_Triv x phi) ) /\
    (forall G D p1 p2  (H : Iso G D p1 p2 ),
       forall x y, y `notin` dom G -> x `notin` tmdom G ->
        Iso (rename_context_co y x G) (rename_atoms y x D)
            (co_subst_co_constraint g_Triv x p1)
            (co_subst_co_constraint g_Triv x p2) ) /\
    (forall G D A B T R (H : DefEq G D A B T R),
       forall x y, y `notin` dom G -> x `notin` tmdom G ->
         DefEq (rename_context_co y x G) (rename_atoms y x D)
               (co_subst_co_tm g_Triv x A) (co_subst_co_tm g_Triv x B)
               (co_subst_co_tm g_Triv x T) R) /\
    (forall G (H : Ctx G),
        forall x y, y `notin` dom G -> x `notin` tmdom G ->
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
        - eapply E_Abs with
             (L := singleton y \u singleton x \u L); eauto.
          intros. move: (H x0 ltac:(auto) x y) => h.
          simpl in *. rewrite rename_atom_diff_same in h. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
          rewrite (co_subst_co_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
          rewrite (co_subst_co_tm_fresh_eq (a_Var_f x0)) in h.
          simpl; auto. apply h; auto.
          intros. destruct rho. eauto.
          replace (a_Var_f x0) with (co_subst_co_tm g_Triv x (a_Var_f x0)).
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
          + eauto.
          + intros. destruct rho. eauto.
          replace (a_Var_f x0) with (co_subst_co_tm g_Triv x (a_Var_f x0)).
          rewrite <- co_subst_co_tm_open_tm_wrt_tm. econstructor.
          rewrite fv_tm_tm_tm_co_subst_co_tm_upper.
          move: (r x0 ltac:(auto)) => h. inversion h; subst. eauto. eauto.
          apply co_subst_co_tm_fresh_eq; eauto.
          + intros. destruct rho. eauto.
          replace (a_Var_f x0) with (co_subst_co_tm g_Triv x (a_Var_f x0)).
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
          move: (CasePath_subst_co x c lc_g_Triv) => h.
          eauto. move: (CasePath_subst_co x c0 lc_g_Triv) => h0. eauto.
          eauto. eauto. eauto. eauto.
          move: (H3 x y ltac:(auto) ltac:(auto)) => h. 
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto. eapply h.
          move: (H4 x y ltac:(auto) ltac:(auto)) => h.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto. eauto.
        - eapply E_LeftIrrel.
          move: (CasePath_subst_co x c lc_g_Triv) => h.
          eauto. move: (CasePath_subst_co x c0 lc_g_Triv) => h0. eauto.
          eauto. eauto. eauto. eauto.
          move: (H3 x y ltac:(auto) ltac:(auto)) => h. 
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto. eapply h.
          move: (H4 x y ltac:(auto) ltac:(auto)) => h.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto. eauto.
        - eapply E_Right.
          move: (CasePath_subst_co x c lc_g_Triv) => h.
          eauto. move: (CasePath_subst_co x c0 lc_g_Triv) => h0. eauto.
          eauto. eauto. eauto. eauto.
          move: (H3 x y ltac:(auto) ltac:(auto)) => h. 
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto. eapply h.
          move: (H4 x y ltac:(auto) ltac:(auto)) => h.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto.
          rewrite co_subst_co_tm_open_tm_wrt_tm in h. eauto. eauto.
        - eapply E_CLeft.
          move: (CasePath_subst_co x c lc_g_Triv) => h.
          eauto. move: (CasePath_subst_co x c0 lc_g_Triv) => h0. eauto.
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

Fixpoint left_list (l : list (atom * atom)) :=
   match l with
   | nil => nil
   | (y, x) :: l' => y :: (left_list l')
   end.

Fixpoint right_list (l : list (atom * atom)) :=
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
      (forall z, z `in` codom (rename_context_tm y x G) ->
                                  z `in` codom G \/ z = y).
Proof. induction G; intros; eauto. destruct a. destruct s; simpl in *. eauto.
       apply union_iff in H. inversion H; clear H.
       - unfold rename_atom in H0.
         destruct (a == x). apply singleton_iff in H0. subst. auto.
         apply singleton_iff in H0. subst. auto.
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
      (forall x, x `in` codom (list_rename_context_tm l G) ->
                      x `in` codom G \/ In x (left_list l)).
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

Lemma list_tm_rename_mutual :
    forall l G, NoDup (left_list l) -> NoDup (right_list l) ->
                disj_list_list (left_list l) (right_list l) ->
                disj_list_set (left_list l) (dom G) ->
                disj_list_set (right_list l) (codom G) ->
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
   fold_left (fun z yx => co_subst_co_tm g_Triv yx.2 z) l A.

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
      (forall z, z `in` tmdom (rename_context_co y x G) ->
                                  z `in` tmdom G \/ z = y).
Proof. induction G; intros; eauto. destruct a. destruct s; simpl in *; eauto.
       apply union_iff in H. inversion H; clear H.
       - unfold rename_atom in H0.
         destruct (a == x). apply singleton_iff in H0. subst. auto.
         apply singleton_iff in H0. subst. auto.
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
      (forall x, x `in` tmdom (list_rename_context_co l G) ->
                      x `in` tmdom G \/ In x (left_list l)).
Proof. induction l; eauto.
       intros. destruct a. simpl in *.
       move: (IHl (rename_context_co a a0 G) x H) => h.
       inversion h; clear h. apply rename_context_co_tmdom in H0.
       inversion H0; auto. auto.
Qed.

(* ------------------------------------------------------------- *)

(* Lemmas on commutativity of two rename operations for tms, sorts, contexts *)

Lemma subst_commute_tm_co : forall A x1 x2, x1 <> x2 ->
      co_subst_co_tm g_Triv x2 (co_subst_co_tm g_Triv x1 A) =
      co_subst_co_tm g_Triv x1 (co_subst_co_tm g_Triv x2 A).
Proof. intros. rewrite co_subst_co_tm_co_subst_co_tm; eauto.
Qed.

Lemma subst_commute_sort_co : forall s x1 x2, x1 <> x2 ->
      co_subst_co_sort g_Triv x2 (co_subst_co_sort g_Triv x1 s) =
      co_subst_co_sort g_Triv x1 (co_subst_co_sort g_Triv x2 s).
Proof. intros. destruct s; simpl; f_equal.
       rewrite co_subst_co_tm_co_subst_co_tm; eauto.
       rewrite co_subst_co_constraint_co_subst_co_constraint; eauto.
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

Lemma list_rename_rename_commute_co : forall l x b,
      ~In x (left_list l) -> ~In x (right_list l) ->
      list_rename_co l (co_subst_co_tm g_Triv x b) =
      co_subst_co_tm g_Triv x (list_rename_co l b).
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

Lemma list_co_rename_mutual :
    forall l G, NoDup (left_list l) -> NoDup (right_list l) ->
                disj_list_list (left_list l) (right_list l) ->
                disj_list_set (left_list l) (dom G) ->
                disj_list_set (right_list l) (tmdom G) ->
    (forall b B (H : Typing G b B),
        Typing (list_rename_context_co l G)
               (list_rename_co l b)
               (list_rename_co l B)).
Proof. induction l; intros; eauto.
       destruct a; simpl in *.
       unfold disj_list_list in *. unfold disj_list_set in *.
       rewrite list_rename_rename_commute_co. intro. apply (H1 a0).
       simpl; auto. simpl; auto. inversion H0; subst; auto.
       rewrite list_rename_rename_commute_co. intro. apply (H1 a0).
       simpl; auto. simpl; auto. inversion H0; subst; auto.
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

