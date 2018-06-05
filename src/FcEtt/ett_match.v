Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Import FcEtt.utils.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.
Require Export FcEtt.toplevel.
Require Export FcEtt.fix_typing.

Require Import Coq.Sorting.Permutation.

Fixpoint matchsubst a p b : tm := match (a,p) with
  | (a_Fam F, a_Fam F') => b
  | (a_App a1 (Role Nom) a2, a_App p1 (Role Nom) (a_Var_f x)) =>
         tm_subst_tm_tm a2 x (matchsubst a1 p1 b)
  | (a_App a1 (Role Rep) a2, a_App p1 (Role Rep) (a_Var_f x)) =>
         tm_subst_tm_tm a2 x (matchsubst a1 p1 b)
  | (a_App a1 (Rho Irrel) a_Bullet, a_App p1 (Rho Irrel) a_Bullet) =>
         matchsubst a1 p1 b
  | (a_CApp a1 g_Triv, a_CApp p1 g_Triv) => matchsubst a1 p1 b
  | (_,_) => b
  end.

Lemma MatchSubst_matchsubst : forall a p b b',
      MatchSubst a p b b' -> matchsubst a p b = b'.
Proof. intros. induction H.
        - simpl. auto.
        - destruct R; simpl. rewrite IHMatchSubst. auto.
          rewrite IHMatchSubst. auto.
        - simpl. auto.
        - simpl. auto.
Qed.

Corollary MatchSubst_function : forall a p b b1 b2,
      MatchSubst a p b b1 -> MatchSubst a p b b2 -> b1 = b2.
Proof. intros. apply MatchSubst_matchsubst in H.
       apply MatchSubst_matchsubst in H0. rewrite H in H0. auto.
Qed.

Inductive Path_pat_consist : tm -> tm -> Prop :=
  | Path_consist_Fam : forall F, Path_pat_consist (a_Fam F) (a_Fam F)
  | Path_consist_AppR : forall a1 p1 a2 x R, Path_pat_consist a1 p1 -> lc_tm a2 ->
       Path_pat_consist (a_App a1 (Role R) a2) (a_App p1 (Role R) (a_Var_f x))
  | Path_consist_IApp : forall a1 p1, Path_pat_consist a1 p1 ->
       Path_pat_consist (a_App a1 (Rho Irrel) a_Bullet)
                        (a_App p1 (Rho Irrel) a_Bullet)
  | Path_consist_CApp : forall a1 p1, Path_pat_consist a1 p1 ->
       Path_pat_consist (a_CApp a1 g_Triv) (a_CApp p1 g_Triv).

Hint Constructors Path_pat_consist.

Lemma MatchSubst_consist : forall a p b b', MatchSubst a p b b' ->
                                            Path_pat_consist a p.
Proof. intros. induction H; eauto.
Qed.

Corollary MatchSubst_nexists : forall a p, ~(Path_pat_consist a p) ->
                      forall b b', ~(MatchSubst a p b b').
Proof. intros. intro H'. apply MatchSubst_consist in H'. contradiction.
Qed.

Lemma MatchSubst_exists : forall a p, Path_pat_consist a p -> forall b,
                          lc_tm b -> exists b', MatchSubst a p b b'.
Proof. intros a p H. induction H; intros.
        - exists b; auto.
        - pose (P := IHPath_pat_consist b H1). inversion P as [b1 Q].
          exists (tm_subst_tm_tm a2 x b1). eauto.
        - pose (P := IHPath_pat_consist b H0). inversion P as [b1 Q].
          exists b1; eauto.
        - pose (P := IHPath_pat_consist b H0). inversion P as [b1 Q].
          exists b1; eauto.
Qed.

Lemma matchsubst_MatchSubst : forall a p b b', Path_pat_consist a p -> lc_tm b ->
      matchsubst a p b = b' -> MatchSubst a p b b'.
Proof. intros. generalize dependent b. generalize dependent b'.
       induction H; intros; eauto.
        - simpl in H1. rewrite <- H1. auto.
        - destruct R. simpl in H2. rewrite <- H2. eauto.
          simpl in H2. rewrite <- H2. eauto.
Qed.

Inductive Pattern : tm -> Prop :=
  | Pattern_Fam : forall F, Pattern (a_Fam F)
  | Pattern_AppR : forall a1 R x, Pattern a1 -> Pattern (a_App a1 (Role R) (a_Var_f x))
  | Pattern_IApp : forall a1, Pattern a1 -> Pattern (a_App a1 (Rho Irrel) a_Bullet)
  | Pattern_CApp : forall a1, Pattern a1 -> Pattern (a_CApp a1 g_Triv).

Hint Constructors Pattern.

Lemma Path_pat_consist_pat : forall a p, Path_pat_consist a p -> Pattern p.
Proof. intros. induction H; eauto.
Qed.

Fixpoint chain_substitution (l : list (atom * tm)) (b : tm) : tm :=
   match l with
   | nil => b
   | (x, a) :: l' => tm_subst_tm_tm a x (chain_substitution l' b)
   end.

Fixpoint permutation (a p : tm) : list (atom * tm) := match (a,p) with
  | (a_Fam F, a_Fam F') => nil
  | (a_App a1 (Role Nom) a2, a_App p1 (Role Nom) (a_Var_f x)) =>
         (x, a2) :: permutation a1 p1
  | (a_App a1 (Role Rep) a2, a_App p1 (Role Rep) (a_Var_f x)) =>
         (x, a2) :: permutation a1 p1
  | (a_App a1 (Rho Irrel) a_Bullet, a_App p1 (Rho Irrel) a_Bullet) =>
         permutation a1 p1
  | (a_CApp a1 g_Triv, a_CApp p1 g_Triv) => permutation a1 p1
  | (_,_) => nil
  end.

Lemma MatchSubst_permutation : forall a p b,
              chain_substitution (permutation a p) b = matchsubst a p b.
Proof. intros. generalize dependent p. generalize dependent b.
       induction a; intros; eauto.
       all: try destruct g; try destruct nu; eauto.
       all: try destruct R; try destruct rho; eauto.
        - destruct p; eauto. destruct nu; eauto. destruct R; eauto.
          destruct p2; eauto. simpl. rewrite IHa1. auto.
        - destruct p; eauto. destruct nu; eauto. destruct R; eauto.
          destruct p2; eauto. simpl. rewrite IHa1. auto.
        - destruct a2; eauto. destruct p; eauto. destruct nu; eauto.
          destruct rho; eauto. destruct p2; eauto.
        - destruct p; eauto. destruct g; eauto.
        - destruct p; eauto.
Qed.

Inductive ICApp : tm -> tm -> Prop :=
   | ICApp_refl : forall a, ICApp a a
   | ICApp_IApp : forall a1 a2, ICApp a1 a2 -> ICApp a1 (a_App a2 (Rho Irrel) a_Bullet)
   | ICApp_CApp : forall a1 a2, ICApp a1 a2 -> ICApp a1 (a_CApp a2 g_Triv).

Lemma nonempty_perm : forall a p x l, x :: l = permutation a p ->
      exists a1 a2 p1 y, (ICApp (a_App a1 (Role Nom) a2) a /\ 
              ICApp (a_App p1 (Role Nom) (a_Var_f y)) p /\ x = (y, a2)
              /\ l = permutation a1 p1) \/
              (ICApp (a_App a1 (Role Rep) a2) a /\ 
              ICApp (a_App p1 (Role Rep) (a_Var_f y)) p /\ x = (y, a2)
              /\ l = permutation a1 p1).
Proof. intros a. induction a; intros p y l H; try (inversion H; fail).
       destruct nu; try (inversion H; fail).
       destruct R; try (inversion H; fail).
       destruct p; try (inversion H; fail).
       destruct nu; try (inversion H; fail).
       destruct R; try (inversion H; fail).
       destruct p2; try (inversion H; fail).
       inversion H. exists a1, a2, p1, x. left; repeat split.
       eapply ICApp_refl. eapply ICApp_refl.
       destruct p; try (inversion H; fail).
       destruct nu; try (inversion H; fail).
       destruct R; try (inversion H; fail).
       destruct p2; try (inversion H; fail).
       inversion H. exists a1, a2, p1, x. right; repeat split.
       eapply ICApp_refl. eapply ICApp_refl.
       destruct rho; try (inversion H; fail).
       destruct a2; try (inversion H; fail).
       destruct p; try (inversion H; fail).
       destruct nu; try (inversion H; fail).
       destruct rho; try (inversion H; fail).
       destruct p2; try (inversion H; fail).
       simpl in H. pose (P := IHa1 p1 y l ltac:(auto)).
       inversion P as [a2 [a3 [p2 [y0 [Q1 | Q2]]]]]. 
       exists a2, a3, p2, y0. inversion Q1 as [S1 [S2 [S3 S4]]].
       left; repeat split.
       eapply ICApp_IApp; auto.
       eapply ICApp_IApp; auto. auto. auto.
       exists a2, a3, p2, y0. inversion Q2 as [T1 [T2 [T3 T4]]]. 
       right; repeat split.
       eapply ICApp_IApp; auto.
       eapply ICApp_IApp; auto. auto. auto.
       destruct g; try (inversion H; fail).
       destruct p; try (inversion H; fail).
       destruct g; try (inversion H; fail).
       simpl in H. pose (P := IHa p y l ltac:(auto)).
       inversion P as [a2 [a3 [p2 [y0 [Q1 | Q2]]]]]. 
       exists a2, a3, p2, y0. inversion Q1 as [S1 [S2 [S3 S4]]].
       left; repeat split.
       eapply ICApp_CApp; auto.
       eapply ICApp_CApp; auto. auto. auto.
       exists a2, a3, p2, y0. inversion Q2 as [T1 [T2 [T3 T4]]]. 
       right; repeat split.
       eapply ICApp_CApp; auto.
       eapply ICApp_CApp; auto. auto. auto.
       destruct p; try (inversion H; fail).
Qed.

Lemma fv_ICApp : forall a1 a2 x, ICApp a1 a2 -> x `in` fv_tm_tm_tm a1 <->
                  x `in` fv_tm_tm_tm a2.
Proof. intros. generalize dependent x.
       induction H; intro.
         - split; auto.
         - pose (P := IHICApp x). inversion P as [P1 P2].
           split; intro; simpl in *; fsetdec.
         - pose (P := IHICApp x). inversion P as [P1 P2].
           split; intro; simpl in *; fsetdec.
Qed.

Lemma fv_perm_1 : forall a p l x a', l = permutation a p -> In (x,a') l ->
                    x `in` fv_tm_tm_tm p.
Proof. intros. generalize dependent a. generalize dependent p.
       dependent induction l; intros. inversion H0.
       inversion H0. subst. apply nonempty_perm in H.
       inversion H as [a1 [a2 [p1 [y [Q1 | Q2]]]]].
       inversion Q1 as [S1 [S2 [S3 S4]]].
       eapply (fv_ICApp x) in S2. inversion S3; subst. simpl in S2.
       fsetdec. inversion Q2 as [T1 [T2 [T3 T4]]].
       eapply (fv_ICApp x) in T2. inversion T3; subst. simpl in T2.
       fsetdec. apply nonempty_perm in H.
       inversion H as [a1 [a2 [p1 [y [Q1 | Q2]]]]].
       inversion Q1 as [S1 [S2 [S3 S4]]].
       eapply (fv_ICApp x) in S2. apply S2. simpl. apply union_iff.
       left. eapply IHl; eauto.
       inversion Q2 as [T1 [T2 [T3 T4]]].
       eapply (fv_ICApp x) in T2. apply T2. simpl. apply union_iff.
       left. eapply IHl; eauto.
Qed.

Lemma fv_perm_2 : forall a p l x a', l = permutation a p -> In (x,a') l ->
                  forall y, y `in` fv_tm_tm_tm a' -> y `in` fv_tm_tm_tm a.
Proof. intros. generalize dependent a. generalize dependent p.
       dependent induction l; intros. inversion H0.
       inversion H0. subst. apply nonempty_perm in H.
       inversion H as [a1 [a2 [p1 [z [Q1 | Q2]]]]].
       inversion Q1 as [S1 [S2 [S3 S4]]].
       eapply (fv_ICApp y) in S1. inversion S3; subst. simpl in S1.
       fsetdec. inversion Q2 as [T1 [T2 [T3 T4]]].
       eapply (fv_ICApp y) in T1. inversion T3; subst. simpl in T1.
       fsetdec. apply nonempty_perm in H.
       inversion H as [a1 [a2 [p1 [z [Q1 | Q2]]]]].
       inversion Q1 as [S1 [S2 [S3 S4]]].
       eapply (fv_ICApp y) in S1. apply S1. simpl. apply union_iff.
       left. eapply IHl; eauto.
       inversion Q2 as [T1 [T2 [T3 T4]]].
       eapply (fv_ICApp y) in T1. apply T1. simpl. apply union_iff.
       left. eapply IHl; eauto.
Qed.

Fixpoint rang (L : list (atom * tm)) : atoms :=
   match L with
   | nil => empty
   | (x, a) :: l => fv_tm_tm_tm a \u rang l
   end.

Lemma dom_Perm : forall A (L : list (atom * A)) L', Permutation L L' ->
                                                        dom L [=] dom L'.
Proof. intros. induction H; eauto. fsetdec. destruct x; simpl. fsetdec.
       destruct x, y. simpl. fsetdec. eapply transitivity; eauto.
Qed.

Lemma rang_Perm : forall L L', Permutation L L' -> rang L [=] rang L'.
Proof. intros. induction H; eauto. fsetdec. destruct x; simpl. fsetdec.
       destruct x, y. simpl. fsetdec. eapply transitivity; eauto.
Qed.

Lemma uniq_Perm : forall A (L : list (atom * A)) L', Permutation L L' ->
                                                      uniq L -> uniq L'.
Proof. intros. induction H; eauto. destruct x. apply uniq_cons_iff in H0.
       inversion H0. eapply uniq_cons_3; eauto. apply dom_Perm in H. fsetdec.
       destruct x, y. solve_uniq.
Qed.

Lemma Chain_sub_Permutation : forall b L L',
        uniq L -> (forall x, x `in` dom L -> x `notin` rang L) ->
        Permutation L L' -> chain_substitution L b = chain_substitution L' b.
Proof. intros.
       dependent induction H1; intros.
         - auto.
         - simpl. destruct x. erewrite IHPermutation; eauto 1.
           solve_uniq. intros. simpl in H0. pose (P := H0 x ltac:(auto)).
           fsetdec.
         - destruct x, y. simpl. rewrite tm_subst_tm_tm_tm_subst_tm_tm.
           rewrite (tm_subst_tm_tm_fresh_eq t). auto. simpl in H0.
           pose (P := H0 a0 ltac:(auto)). fsetdec. simpl in H0.
           pose (P := H0 a ltac:(auto)). fsetdec.
           solve_uniq.
         - apply transitivity with (y := chain_substitution l' b).
           eapply IHPermutation1; eauto. eapply IHPermutation2.
           eapply uniq_Perm; eauto. pose (P := H1_). pose (Q := H1_).
           apply dom_Perm in P. apply rang_Perm in Q. intros.
           pose (S := H0 x). fsetdec.
Qed.

Definition Nice a p := Path_pat_consist a p /\
              (forall x, x `in` fv_tm_tm_tm p -> x `notin` fv_tm_tm_tm a) /\
               uniq (permutation a p).

Fixpoint matchsubst2 a p b : tm := match (a,p) with
  | (a_Fam F, a_Fam F') => if F == F' then b else a_Bullet
  | (a_App a1 (Role Nom) a2, a_App p1 (Role Nom) (a_Var_f x)) =>
         tm_subst_tm_tm a2 x (matchsubst a1 p1 b)
  | (a_App a1 (Role Rep) a2, a_App p1 (Role Rep) (a_Var_f x)) =>
         tm_subst_tm_tm a2 x (matchsubst a1 p1 b)
  | (a_App a1 (Rho Irrel) a_Bullet, a_App p1 (Rho Irrel) a_Bullet) =>
         matchsubst a1 p1 b
  | (a_CApp a1 g_Triv, a_CApp p1 g_Triv) => matchsubst a1 p1 b
  | (_,_) => a_Bullet
  end.

Lemma matchsubst_subst : forall a p b x y, x `notin` fv_tm_tm_tm a ->
      y `notin` fv_tm_tm_tm a -> matchsubst2 a p b =
    matchsubst2 a (tm_subst_tm_tm (a_Var_f y) x p) (tm_subst_tm_tm (a_Var_f y) x b).
Proof. intros. generalize dependent p. generalize dependent b.
       induction a; intros; eauto.
         - destruct nu; eauto. destruct R; eauto.
           destruct p; eauto. simpl. destruct (x0 == x); auto.
           destruct nu; eauto. destruct R; eauto. destruct p2; eauto.
           simpl. destruct (x0 == x); auto.

Fixpoint matchsubst2 a p b : tm := match (a,p) with
  | (a_Fam F, a_Fam F') => if F == F' then b else a_Bullet
  | (a_App a1 (Role Nom) a2, a_App p1 (Role Nom) (a_Var_f x)) =>
         matchsubst2 a1 p1 (tm_subst_tm_tm a2 x b)
  | (a_App a1 (Role Rep) a2, a_App p1 (Role Rep) (a_Var_f x)) =>
         matchsubst2 a1 p1 (tm_subst_tm_tm a2 x b)
  | (a_App a1 (Rho Irrel) a_Bullet, a_App p1 (Rho Irrel) a_Bullet) =>
         matchsubst a1 p1 b
  | (a_CApp a1 g_Triv, a_CApp p1 g_Triv) => matchsubst a1 p1 b
  | (_,_) => a_Bullet
  end.

Lemma matchsubst_matchsubst2 : forall a p b,
      (forall x, x `in` fv_tm_tm_tm a -> x `notin` fv_tm_tm_tm p) ->
       matchsubst a p b = matchsubst2 a p b.
Proof. intros. generalize dependent p. generalize dependent b.
       induction a; intros; eauto. destruct p; eauto.
       destruct p2; eauto. destruct nu; eauto.
       destruct nu0; eauto. destruct R, R0; eauto; simpl.


Lemma MatchSubst_lc_1 : forall a p b b', MatchSubst a p b b' →  lc_tm a.
Proof.
  induction 1; auto.
Qed.

Lemma MatchSubst_lc_2 : forall a p b b', MatchSubst a p b b' →  lc_tm b.
Proof.
  induction 1; auto.
Qed.

Lemma MatchSubst_lc_3 : forall a p b b', MatchSubst a p b b' →  lc_tm b'.
Proof.
  induction 1;
    eauto using tm_subst_tm_tm_lc_tm, co_subst_co_tm_lc_tm.
Qed.

Lemma ax_const_rs_nil : forall F F0 a A R Rs S, Sig S ->
                 binds F (Ax (a_Fam F0) a A R Rs) S -> F = F0 /\ Rs = nil.
Proof. intros. induction H. inversion H0. inversion H0.
       inversion H3. eauto. inversion H0. inversion H5; subst.
       inversion H2; subst. inversion H2; auto. eauto.
Qed.

Lemma match_subst_roleing : forall W a R p b b', Roleing W a R ->
                   MatchSubst a p b b' -> Roleing W b' R.
Proof. Admitted.

Lemma match_path : forall F p a A R Rs a0 b, binds F (Ax p a A R Rs) toplevel ->
                          MatchSubst a0 p a b -> Path a0 F nil.
Proof. intros. induction H0. pose (H' := H).
       eapply ax_const_rs_nil in H'. inversion H'; subst.
       eauto. apply Sig_toplevel. econstructor. auto.
       Admitted.


Lemma ApplyArgs_lc_3 : forall a b c, ApplyArgs a b c → lc_tm c.
Proof.
  induction 1; lc_solve.
Qed.
