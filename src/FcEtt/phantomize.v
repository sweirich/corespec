(* This file shows that we don't need irrelevant arguments in the presence of
   the phantom role.

   - After compiling irrelevant arguments to phm, the operational semantics is
     the same.

   - After compiling irrelevant arguments to phm, the terms will still type
     check (phantomize_mutual).

   - Do we need to show anything else?


*)



Require Import FcEtt.ett_ind.
Require Import FcEtt.ett_value.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

(* ----------------------------------------------------------- *)
(* Translate all uses of irrelevant arguments to phantom roles *)
(* ----------------------------------------------------------- *)

Fixpoint phantomize (a : tm) := 
   match a with
   | a_Star    => a_Star
   | a_Var_b n => a_Var_b n
   | a_Var_f x => a_Var_f x

   | a_UAbs Rel R b   => a_UAbs Rel R (phantomize b)
   | a_UAbs Irrel R b => a_UAbs Rel Phm (phantomize b)

   | a_Abs Rel A R b   => a_Abs Rel (phantomize A) R   (phantomize b)
   | a_Abs Irrel A R b => a_Abs Rel (phantomize A) Phm (phantomize b)

   | a_App a Rel R b   => a_App (phantomize a) Rel R   (phantomize b)
   | a_App a Irrel R b => a_App (phantomize a) Rel Phm (phantomize b)

   | a_Pi Rel   A R B => a_Pi Rel (phantomize A) R   (phantomize B)
   | a_Pi Irrel A R B => a_Pi Rel (phantomize A) Phm (phantomize B)

   | a_Fam F => a_Fam F

   (* TODO: phantomize coercion proofs? *)
   | a_Conv a r1 g => a_Conv (phantomize a) r1 g_Triv

   | a_CPi phi B => a_CPi (phantomize_constraint phi) (phantomize B)
   | a_CAbs phi b => a_CAbs (phantomize_constraint phi) (phantomize b)
   | a_UCAbs b => a_UCAbs (phantomize b)
   | a_CApp a g => a_CApp (phantomize a) g_Triv
   | a_DataCon K => a_Star  (* a_DataCon K *)
   | a_Case a brs => a_Star (* a_Case (phantomize a) (erase_brs brs) *)
   | a_Bullet => a_Bullet
   | a_Sub r a => a_Sub r (phantomize a)
   end
with phantomize_brs (x : brs) : brs := 
   match x with
   | br_None => br_None
   | br_One k a y => br_One k (phantomize a) (phantomize_brs y)
   end
with phantomize_constraint (phi : constraint) : constraint :=
   match phi with
   | Eq A B A1 R => Eq (phantomize A) (phantomize B) (phantomize A1) R
   end.

Definition phantomize_sort (s : sort) : sort := 
  match s with 
  | Tm A R => Tm (phantomize A) R 
  | Co phi => Co (phantomize_constraint phi)
  end.

Definition phantomize_context (G : context) :=
  map phantomize_sort G.

(* -------------------------------------------------------- *)

(* Locally-nameless properties of the "phantomize" function
   See: erase_syntax for inspiration of the sorts of 
   properties that we should prove here. 
*)

Lemma phantomize_open_rec : forall a,
  (forall b k, phantomize (open_tm_wrt_tm_rec k a b) =
               open_tm_wrt_tm_rec k (phantomize a) (phantomize b)) /\
  (forall b k, phantomize_brs (open_brs_wrt_tm_rec k a b) =
               open_brs_wrt_tm_rec k (phantomize a) (phantomize_brs b)) /\
  (forall g:co, True) /\
  (forall b k, phantomize_constraint (open_constraint_wrt_tm_rec k a b) =
               open_constraint_wrt_tm_rec k (phantomize a) (phantomize_constraint b)).
Proof. intro a.
  eapply tm_brs_co_constraint_mutind;
  intros; simpl; auto; try (rewrite H; try rewrite H0; auto).
  case (lt_eq_lt_dec n k);intro P; simpl; auto. destruct P; auto.
  all: f_equal; simpl; eauto 2.
  all: destruct rho; try (rewrite H; rewrite H0); eauto.
Qed.

Lemma phantomize_open : forall a b,
  phantomize (open_tm_wrt_tm a b) = open_tm_wrt_tm (phantomize a) (phantomize b).
Proof.
  intros a b.
  case (phantomize_open_rec b).
  eauto.
Qed.

Lemma phantomize_open_co_rec : forall a,
  (forall b k, (open_tm_wrt_co_rec k a (phantomize b)) =
                 phantomize (open_tm_wrt_co_rec k a b)) /\
  (forall b k, open_brs_wrt_co_rec k a (phantomize_brs b) =
                 phantomize_brs (open_brs_wrt_co_rec k a b)) /\
  (forall g:co, True) /\
  (forall b k, open_constraint_wrt_co_rec k a (phantomize_constraint b) =
                 phantomize_constraint (open_constraint_wrt_co_rec k a b)).
Proof.
  intro a.
  eapply tm_brs_co_constraint_mutind;
  intros; simpl; auto; try (rewrite <- H; try rewrite <- H0; auto).
  all: f_equal; eauto 2.
  all: destruct rho; try (rewrite <- H; rewrite <- H0); eauto.
Qed.

Lemma phantomize_open_co : forall a b,
  open_tm_wrt_co (phantomize b) a = phantomize (open_tm_wrt_co b a).
Proof.
  intros a b.
  destruct (phantomize_open_co_rec a).
  eauto.
Qed.

Lemma phantomize_open' : forall a b,
  open_tm_wrt_tm (phantomize a) (phantomize b) = phantomize (open_tm_wrt_tm a b).
Proof. intros. rewrite phantomize_open; auto.
Qed.

Lemma phantomize_lc :
  (forall a, lc_tm a -> lc_tm (phantomize a)) /\
  (forall b, lc_brs b -> lc_brs (phantomize_brs b)) /\
  (forall (g:co) (l:lc_co g), True) /\
  (forall b, lc_constraint b -> lc_constraint (phantomize_constraint b)).
Proof. eapply lc_tm_lc_brs_lc_co_lc_constraint_mutind.
  all: intros.
  all: try solve [try destruct rho; simpl; eauto].
  all: try destruct rho; simpl.
  all: try (econstructor; auto; intro x; try (pose (P := H0 x));
    try (pose (P := H x)); rewrite <- phantomize_open' in P; eauto; fail).
  all: try destruct phi; simpl.
  all: (econstructor; auto; intro; rewrite phantomize_open_co; auto).
Qed.

Lemma phantomize_dom : forall G, dom G = dom (phantomize_context G).
Proof.
  induction G. simpl. auto.
  destruct a. simpl. rewrite IHG. eauto.
Qed.

(* -------------------------------------------------------- *)
(* Proofs that we actually care about.                      *)

Lemma Path_phantomize:
      forall F a R, Path F a R -> Path F (phantomize a) R.
Proof. intros. induction H; simpl; eauto.
       destruct rho; simpl. econstructor. apply phantomize_lc; auto. auto.
       econstructor. apply phantomize_lc; auto. auto.
Qed.

Lemma CoercedValue_Value_phantomize:
  (forall R v,  CoercedValue R v -> CoercedValue R (phantomize v)) /\
  (forall R v, Value R v -> Value R (phantomize v)).
Proof. apply CoercedValue_Value_mutual; eauto.
       all: intros; simpl.
        - eapply CC. auto.
        - eapply CCV; eauto.
        - destruct rho; econstructor.
          apply phantomize_lc; auto.
          apply phantomize_lc in l0; eauto.
          apply phantomize_lc; auto.
          apply phantomize_lc in l0; eauto.
        - destruct phi. econstructor.
          apply phantomize_lc; auto.
          apply phantomize_lc in l0; eauto.
        - econstructor. apply phantomize_lc; auto.
          apply phantomize_lc in l0; eauto.
        - econstructor. apply phantomize_lc in l; eauto.
        - econstructor. pick fresh x. eapply lc_a_UAbs_exists with (x1 := x).
          pose (P := H x). apply CoercedValue_Value_lc in P; auto.
          rewrite phantomize_open in P. eauto.
        - destruct phi. econstructor. apply phantomize_lc in l.
          auto. apply phantomize_lc in l0. auto.
        - econstructor. apply phantomize_lc in l. auto.
        - econstructor; eauto.
        - destruct rho. econstructor. apply phantomize_lc; auto.
          eapply Path_phantomize; eauto. auto. econstructor.
          apply phantomize_lc; auto. eapply Path_phantomize; eauto. auto.
        - econstructor; auto. eapply Path_phantomize; eauto.
Qed.

Lemma phantomize_Beta :
  forall a b R, Beta a b R -> Beta (phantomize a) (phantomize b) R.
Proof.
  intros a b R H.
  destruct H; simpl.
  - destruct rho. rewrite phantomize_open.
    econstructor. apply phantomize_lc. auto. econstructor.
    inversion H0; subst. inversion H3; subst.
    econstructor. intro x. pose (P := H2 x). apply phantomize_lc in P.
    rewrite phantomize_open in P. auto.
    rewrite phantomize_open.
    econstructor. apply phantomize_lc. auto.
    apply CoercedValue_Value_phantomize in H0. eauto.
  - rewrite <- phantomize_open_co. econstructor. apply phantomize_lc in H; auto.
  - admit.
  - econstructor. apply phantomize_lc in H; auto.
Admitted.

Lemma phantomize_reduction_in_one :
  forall a b R, reduction_in_one a b R -> reduction_in_one (phantomize a) (phantomize b) R.
Proof. intros. induction H; simpl; eauto.
        - admit.
        - apply phantomize_lc in H. destruct rho; econstructor; auto.
        - apply phantomize_lc in H. rewrite phantomize_open.
          apply CoercedValue_Value_phantomize in H0.
          destruct rho; econstructor; auto.
        - rewrite <- phantomize_open_co. apply phantomize_lc in H.
          econstructor; auto.
        - admit.
        - apply CoercedValue_Value_phantomize in H. eapply E_Combine; auto.
        - apply CoercedValue_Value_phantomize in H0. apply phantomize_lc in H.
          destruct rho; econstructor; auto.
        - apply CoercedValue_Value_phantomize in H. econstructor; auto.
Admitted.

Lemma sub_mutual :
   (forall G0 b B R (H : Typing G0 b B R),
      forall G a A R', Typing G a A R' ->
         forall F x R'', G0 = (F ++ (x ~ (Tm A R')) ++ G) -> SubRole R'' R' ->
                      Typing (F ++ (x ~ (Tm A R'')) ++ G) b B R) /\
    (forall G0 phi (H : PropWff G0 phi),
        forall G a A R', Typing G a A R' ->
         forall F x R'', G0 = (F ++ (x ~ (Tm A R')) ++ G) -> SubRole R'' R' ->
                        PropWff (F ++ (x ~ (Tm A R'')) ++ G) phi) /\
    (forall G0 D p1 p2 (H : Iso G0 D p1 p2),
        forall G a A R', Typing G a A R' ->
         forall F x R'', G0 = (F ++ (x ~ (Tm A R')) ++ G) -> SubRole R'' R' ->
                Iso (F ++ (x ~ (Tm A R'')) ++ G) D p1 p2) /\
    (forall G0 D A B T R'' (H : DefEq G0 D A B T R''),
       forall G a A0 R', Typing G a A0 R' ->
         forall F x R0, G0 = (F ++ (x ~ (Tm A0 R')) ++ G) -> SubRole R0 R' ->
                 DefEq (F ++ (x ~ (Tm A0 R0)) ++ G) D A B T R'') /\
    (forall G0 (H : Ctx G0),
        forall G a A R', Typing G a A R' ->
         forall F x R'', G0 = (F ++ (x ~ (Tm A R')) ++ G) -> SubRole R'' R' ->
                        Ctx (F ++ (x ~ (Tm A R'')) ++ G)).
Proof. eapply typing_wff_iso_defeq_mutual;
    intros; subst; simpl.
     - eapply E_SubRole with (R1 := R1). auto. eapply H; eauto.
     - eapply E_Star. eapply H; eauto.
     - apply binds_app_1 in b. destruct b. eapply E_Var. eapply H; eauto.
       apply binds_app_2. auto. apply binds_app_1 in H1. destruct H1.
       apply binds_one_iff in H1. destruct H1. inversion H3. subst.
       econstructor. eauto. eapply E_Var. eapply H; eauto. apply binds_app_3.
       apply binds_cons_2; auto. eapply E_Var. eapply H; eauto.
       apply binds_app_3. apply binds_cons_3. auto.
     - eapply E_Pi with (L := L). intros. rewrite <- app_assoc. eapply H; eauto.
       eapply H0; eauto.
     - eapply E_Abs with (L := L). intros. rewrite <- app_assoc. eapply H; eauto.
       eapply H0; eauto. intros; auto.
     - eapply E_App. eapply H; eauto. eapply H0; eauto.
     - eapply E_IApp. eapply H; eauto. eapply H0; eauto.
     - eapply E_Conv. eapply H; eauto.
       assert (dom (F ++ (x, Tm A0 R'') :: G0) = dom (F ++ (x, Tm A0 R') :: G0)).
       admit. rewrite H3. eapply H0; eauto. eapply H1; eauto.
     - eapply E_CPi with (L := L). intros. rewrite <- app_assoc. eapply H; eauto.
       eapply H0; eauto.
     - eapply E_CAbs with (L := L). intros. rewrite <- app_assoc. eapply H; eauto.
       eapply H0; eauto.
     - eapply E_CApp. eapply H; eauto.
       assert (P : dom (F ++ (x, Tm A0 R'') :: G0) = dom (F ++ (x, Tm A0 R'0) :: G0)).
       admit. rewrite P. eapply H0; eauto.
     - eapply E_Fam. eapply H; eauto. eauto. eauto.
     - eapply E_TyCast. eapply H; eauto.
       assert (P : dom (F ++ (x, Tm A R'') :: G0) = dom (F ++ (x, Tm A R') :: G0)).
       admit. rewrite P. eapply H0; eauto. eapply H1; eauto.
     - eapply E_Bullet. eapply H; eauto.
     - econstructor. eapply H; eauto. eapply H0; eauto. eapply H1; eauto.
     - econstructor. eapply H; eauto. eapply H0; eauto.
     - econstructor. eapply H; eauto. eapply H0; eauto. eapply H1; eauto.
     - econstructor. eapply H; eauto.
     - apply binds_app_1 in b0. destruct b0. eapply E_Assn. eapply H; eauto.
       apply binds_app_2. eauto. auto. apply binds_app_1 in H1. destruct H1.
       apply binds_one_iff in H1. destruct H1. inversion H3.
       eapply E_Assn. eapply H; eauto. apply binds_app_3. apply binds_cons_3.
       eauto. auto.
     - eapply E_Refl. eapply H; eauto.
     - eapply E_Sym. eapply H; eauto.
     - eapply E_Trans. eapply H; eauto. eapply H0; eauto.
     - eapply E_Sub. eapply H; eauto. auto.
     - eapply E_Beta. eapply H; eauto. eapply H0; eauto. auto.
     - eapply E_PiCong with (L := L). eapply H; eauto. intros.
       rewrite <- app_assoc. eapply H0; eauto. eapply H1; eauto.
       eapply H2; eauto. eapply H3; eauto.
     - eapply E_AbsCong with (L := L). intros. rewrite <- app_assoc.
       eapply H; eauto. eapply H0; eauto. intros; auto. intros; auto.
     - eapply E_AppCong. eapply H; eauto. eapply H0; eauto.
     - eapply E_IAppCong. eapply H; eauto. eapply H0; eauto.
     - eapply E_PiFst. eapply H; eauto.
     - eapply E_PiSnd. eapply H; eauto. eapply H0; eauto.
     - eapply E_CPiCong with (L := L). eapply H; eauto.
       intros. rewrite <- app_assoc. eapply H0; eauto.
       eapply H1; eauto. eapply H2; eauto. eapply H3; eauto.
     - eapply E_CAbsCong with (L := L). intros. rewrite <- app_assoc.
       eapply H; eauto. eapply H0; eauto.
     - eapply E_CAppCong. eapply H; eauto.
       assert (P : dom (F ++ (x, Tm A0 R0) :: G0) = dom (F ++ (x, Tm A0 R'0) :: G0)).
       admit. rewrite P. eapply H0; eauto.
     - eapply E_CPiSnd. eapply H; eauto.
       assert (P : dom (F ++ (x, Tm A0 R1) :: G0) = dom (F ++ (x, Tm A0 R'0) :: G0)).
       admit. rewrite P. eapply H0; eauto.
       assert (P : dom (F ++ (x, Tm A0 R1) :: G0) = dom (F ++ (x, Tm A0 R'0) :: G0)).
       admit. rewrite P. eapply H1; eauto.
     - eapply E_Cast. eapply H; eauto. eapply H0; eauto.
     - eapply E_EqConv. eapply H; eauto.
       assert (P : dom (F ++ (x, Tm A0 R0) :: G0) = dom (F ++ (x, Tm A0 R') :: G0)).
       admit. rewrite P. eapply H0; eauto. auto.
     - eapply E_IsoSnd. eapply H; eauto.
     - eapply E_CastCong. eapply H; eauto.
       assert (P : dom (F ++ (x, Tm A0 R0) :: G0) = dom (F ++ (x, Tm A0 R') :: G0)).
       admit. rewrite P. eapply H0; eauto. eapply H1; eauto.
     - destruct F. inversion H0. inversion H0.
     - admit.
     - admit.
Admitted.

Lemma phantomize_mutual :
  (forall G a A R, Typing G a A R ->
          Typing (phantomize_context G) (phantomize a) (phantomize A) R) /\
  (forall G phi, PropWff G phi ->
          PropWff (phantomize_context G) (phantomize_constraint phi)) /\
  (forall G D p1 p2, Iso G D p1 p2 ->
          Iso (phantomize_context G) D
              (phantomize_constraint p1) (phantomize_constraint p2)) /\
  (forall G D a b A R,
      DefEq G D a b A R  ->
             DefEq (phantomize_context G) D (phantomize a) (phantomize b) (phantomize A) R) /\
  (forall G, Ctx G -> Ctx (phantomize_context G) /\
   forall c t, binds c t G -> binds c (phantomize_sort t) (phantomize_context G)).
Proof. apply typing_wff_iso_defeq_mutual; intros; repeat split; intros; split_hyp; subst;
  simpl; auto.
    - econstructor; eauto.
    - eapply E_Var; auto. pose (P := H0 _ _ b). eauto.
    - destruct rho. eapply E_Pi with (L := L); auto. intros.
      pose (P := H x ltac:(auto)). rewrite <- phantomize_open' in P. eauto.
      eapply E_Pi with (L := L). intros. pose (P := H x ltac:(auto)).
      rewrite <- phantomize_open' in P. admit. econstructor; eauto.
    - destruct rho. eapply E_Abs with (L := L); auto. intros.
      pose (P := H x ltac:(auto)). rewrite <- phantomize_open' in P.
      rewrite <- phantomize_open' in P. eauto.
      eapply E_Abs with (L := L); auto. intros.
      pose (P := H x ltac:(auto)). rewrite <- phantomize_open' in P.
      rewrite <- phantomize_open' in P. admit. econstructor; eauto.
    - rewrite phantomize_open. eapply E_App; eauto.
    - rewrite phantomize_open. assert (a_Bullet = phantomize a). admit.
      rewrite H1. eapply E_App; eauto.
    - eapply E_Conv. eauto. rewrite <- phantomize_dom. eauto. auto.
    - destruct phi. eapply E_CPi with (L := L). intros.
      rewrite phantomize_open_co. simpl in H. apply H. auto. auto.
    - destruct phi. eapply E_CAbs with (L := L). intros.
      rewrite phantomize_open_co. rewrite phantomize_open_co. simpl in H.
      apply H. auto. auto.
    - rewrite <- phantomize_open_co. eapply E_CApp. simpl in H. eapply H.
      rewrite <- phantomize_dom. auto.
    - eapply E_Fam. auto. admit. auto.
    - rewrite phantomize_dom in H0. eapply E_TyCast; eauto.
    - econstructor; eauto.
    - pose (P := H0 _ _ b0). econstructor; eauto.
    - eapply E_Trans; eauto.
    - eapply E_Sub; eauto.
    - apply phantomize_Beta in b. eapply E_Beta; eauto.
    - destruct rho. eapply E_PiCong with (L := L). eauto. intros.
      pose (P := H0 x ltac:(auto)). rewrite <- phantomize_open' in P.
      rewrite <- phantomize_open' in P. eauto. eauto. eauto. eauto.
      eapply E_PiCong with (L := L). eauto. intros.
      pose (P := H0 x ltac:(auto)). rewrite <- phantomize_open' in P.
      rewrite <- phantomize_open' in P. admit. econstructor; eauto. eauto. eauto.
    - destruct rho. eapply E_AbsCong with (L := L). intros.
      pose (P := H x ltac:(auto)). rewrite <- phantomize_open' in P.
      rewrite <- phantomize_open' in P. rewrite <- phantomize_open' in P.
      eauto. eauto. intros; eauto. intros; eauto.
      eapply E_AbsCong with (L := L). intros.
      pose (P := H x ltac:(auto)). rewrite <- phantomize_open' in P.
      rewrite <- phantomize_open' in P. rewrite <- phantomize_open' in P.
      admit. econstructor; eauto. intros; eauto. intros; eauto.
    - rewrite phantomize_open. eapply E_AppCong; eauto.
    - rewrite phantomize_open. assert (a_Bullet = phantomize a). admit.
      rewrite H1. eapply E_AppCong; eauto.
    - destruct rho. eapply E_PiFst. eauto. simpl in H. admit.
    - rewrite phantomize_open. rewrite phantomize_open. destruct rho.
      eapply E_PiSnd; eauto. simpl in H. eapply E_PiSnd; eauto.
    - eapply E_CPiCong with (L := L). auto. intros.
      pose (P := H0 c ltac:(auto)). rewrite <- phantomize_open_co in P.
      rewrite <- phantomize_open_co in P. all: eauto.
    - destruct phi1. eapply E_CAbsCong with (L := L). intros.
      pose (P := H c ltac:(auto)). rewrite <- phantomize_open_co in P.
      rewrite <- phantomize_open_co in P. rewrite <- phantomize_open_co in P.
      all : eauto.
    - rewrite <- phantomize_open_co. simpl in H. rewrite phantomize_dom in H0.
      eapply E_CAppCong; eauto.
    - rewrite <- phantomize_open_co. rewrite <- phantomize_open_co.
      simpl in H. rewrite phantomize_dom in H0, H1. eapply E_CPiSnd; eauto.
    - eapply E_Cast; eauto.
    - rewrite phantomize_dom in H0. eapply E_EqConv; eauto.
    - eapply E_IsoSnd; eauto.
    - rewrite phantomize_dom in H0. eapply E_CastCong; eauto.
    - rewrite phantomize_dom in n. econstructor; eauto.
    - apply binds_cons_1 in H1. destruct H1. destruct H1. econstructor.
      rewrite H1. rewrite H3. auto. pose (P := H2 _ _ H1). apply binds_cons_3.
      auto.
    - rewrite phantomize_dom in n. econstructor; eauto.
    - apply binds_cons_1 in H1. destruct H1. destruct H1. econstructor.
      rewrite H1. rewrite H3. auto. pose (P := H2 _ _ H1). apply binds_cons_3.
      auto. Unshelve. all: auto.
Admitted.

