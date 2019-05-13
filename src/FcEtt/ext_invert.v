Require Import FcEtt.imports.
Require Import FcEtt.ett_ott.
Require Import FcEtt.ett_inf.
Require Import FcEtt.ett_ind.

Require Import FcEtt.ett_par.
Require Import FcEtt.ext_wf.
Require Import FcEtt.ext_weak.
Require Import FcEtt.ext_subst.

Require Import FcEtt.utils.
Require Import FcEtt.notations.


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


Lemma binds_to_Typing: forall G T A R, Ctx G -> binds T (Tm A R) G -> Typing G A a_Star R.
Proof.
  induction G; try done.
  intros T A R H H0.
  rewrite_env ([a] ++ G).
  destruct a.
  induction s; subst.
  - inversion H0; eauto.
    + inversion H1; subst; clear H1.
      inversion H; subst; eauto.
      all: eapply Typing_weakening with (F:=nil); eauto.
    + eapply Typing_weakening with (F:=nil); eauto 2.
      rewrite_env G.
      eapply IHG; eauto 2.
      inversion H; auto.
  - inversion H0; try done.
    eapply Typing_weakening with (F:=nil); eauto 2.
    rewrite_env G.
    eapply IHG; eauto 2.
    inversion H; auto.
Qed.


Lemma invert_a_Pi:
  forall G rho A0 A B0 R R',
    Typing G (a_Pi rho A0 R B0) A R' ->
    DefEq G (dom G) A a_Star a_Star Rep /\ 
      (exists L, forall x, x `notin` L -> 
        Typing ([(x, Tm A0 R)] ++ G) (open_tm_wrt_tm B0 (a_Var_f x)) a_Star R') 
          /\ Typing G A0 a_Star R.
Proof.
  intros G rho A0 A B0 R R' h1.
  dependent induction h1; auto; try done.
  - pose P := IHh1 rho A0 B0 R eq_refl.
    inversion P as [H1 [H2 H3]]. repeat split; auto.
    inversion H2 as [L H5]. exists L. intros. eapply E_SubRole; eauto.
  - repeat split; eauto.
  - destruct (IHh1_1 rho A0 B0 R) as (h1 & h2 & h3); try reflexivity.
    repeat split; eauto 1.
    destruct R0; eapply E_Trans; eauto.
Qed.

Lemma invert_a_CPi: forall G phi A B0 R,
    Typing G (a_CPi phi B0) A R ->
      DefEq G (dom G) A a_Star a_Star Rep /\ (exists L, forall c, c `notin` L -> Typing ([(c, Co phi)] ++ G) (open_tm_wrt_co B0 (g_Var_f c) ) a_Star R)  /\ PropWff G phi.
Proof.
  intros G phi A B0 R h1.
  dependent induction h1; eauto 2; try done.
  - destruct (IHh1 phi B0) as [h2 [L h3]]; first by done.
    repeat split; eauto 1. inversion L as [L0 h4].
    exists L0. intros. eapply E_SubRole. apply H. auto.
  - destruct (IHh1_1 phi B0) as [h2 [L h3]]; first by done.
    repeat split; eauto 1 using Typing_Ctx. 
    destruct R; eapply E_Trans; eauto.
  - repeat split; eauto 2 using Typing_Ctx. apply E_Refl. 
    apply E_Star. apply PropWff_Ctx in H1. assumption.
Qed.


Lemma invert_a_Fam : forall G F A R,
    Typing G (a_Fam F) A R ->
    exists a B R', DefEq G (dom G) A B a_Star R /\
           binds F (Ax a B R') toplevel /\ Typing nil B a_Star R.
Proof.
  intros G F A R H. dependent induction H.
  - destruct (IHTyping F) as (a & B1 & R' & h0 & h1 & h3); try done.
    exists a, B1, R' . repeat split; eauto.
  - destruct (IHTyping1 F) as (a & B1 & R' & h0 & h1 & h3); try done.
    exists a, B1, R' . repeat split; eauto 2.
    eapply E_Trans with (a1 := A).
    eapply E_Sym. auto. auto.
  - exists a, A, R.
    repeat split; eauto 2.
    eapply E_Refl.
    eapply Typing_weakening with (F:=nil)(E:=G)(G:=nil) in H1.
    simpl_env in H1. auto. auto. simpl_env. auto.
Qed.


Lemma invert_a_Star: forall A G R, Typing G a_Star A R -> DefEq G (dom G) A a_Star a_Star R.
Proof.
  intros A G R H.
  dependent induction H; subst; eauto 2; try done.
  eauto.
  eauto 4. eauto.
Qed.


Lemma invert_a_Var :
  forall G x A R, Typing G (a_Var_f x) A R -> exists A' R', binds x (Tm A' R') G /\ DefEq G (dom G) A A' a_Star R /\ SubRole R' R.
Proof.
  intros G x A R H. dependent induction H. 
  - destruct (IHTyping x eq_refl) as (A0 & R0 & h1 & h2 & h3).
    exists A0, R0. repeat split; eauto 2.
  - exists A, R. repeat split; auto. 
    move: (binds_to_Typing x _ _ H H0) => h0.
    eapply E_Refl; eauto.
  - destruct (IHTyping1 x eq_refl) as [A' [R' [bi [D1 D2]]]].
    exists A', R'. repeat split; auto. eapply E_Trans with (a1:= A).
    eapply E_Sym; eauto.
    auto.
Qed.


(* -------------------------------
   Find a better place for these tactics
*)
Ltac expand sub_tm tm :=
  match tm with
  | (a_Abs ?rho (_ ?A1) ?R (_ ?b)) =>
    replace (a_Abs rho (sub_tm A1) R (sub_tm b)) with (sub_tm (a_Abs rho A1 R b)); auto
  | (a_Pi ?rho (_ ?A1) ?R (_ ?B1)) =>
    replace (a_Pi rho (sub_tm A1) R (sub_tm B1)) with (sub_tm (a_Pi rho A1 R B1)); auto
  | (a_CAbs (?sc ?phi) (_ ?B)) =>
    replace (a_CAbs (sc phi) (sub_tm B)) with (sub_tm (a_CAbs phi B)); auto
  | (a_CPi (?sc ?phi) (_ ?B)) =>
    replace (a_CPi (sc phi) (sub_tm B)) with (sub_tm (a_CPi phi B)); auto

  | a_Star => replace a_Star with (sub_tm a_Star); auto

  | _ => idtac
  end.

Ltac expand_constraint sub_tm sub_constraint constraint :=
  match constraint with
  | (Eq (_ _ _ ?a) (_ _ _  ?b) (_ _ _ ?A) ?R) =>
    replace (Eq (sub_tm a) (sub_tm b) (sub_tm A) R) with
    (sub_constraint (Eq a b A R)); auto
  | _ => idtac
  end.

Ltac un_subst_tm :=
   match goal with
   | [ |- context [tm_subst_tm_tm ?g ?c _] ] =>
     match goal with
     | [ |- Typing _ ?a ?A ?R ] => expand (tm_subst_tm_tm g c) a; expand (tm_subst_tm_tm g c) A
     | [ |- DefEq _ _ ?a ?b ?R ] => expand (tm_subst_tm_tm g c) a; expand (tm_subst_tm_tm g c) b
     | [ |- PropWff ?phi ] => expand_constraint (tm_subst_tm_tm g c) (tm_subst_tm_constraint g c) phi
     end
   | [ |- context [co_subst_co_tm ?g ?c _] ] =>
     match goal with
     | [ |- Typing _ ?a ?A ?R ] => expand (co_subst_co_tm g c) a; expand (co_subst_co_tm g c) A
     | [ |- DefEq _ _ ?a ?b ?R ] => expand (co_subst_co_tm g c) a; expand (co_subst_co_tm g c) b
     | [ |- PropWff ?phi ] => expand_constraint (co_subst_co_tm g c) (co_subst_co_constraint g c) phi
     end
   end.




(* --------------------------------------------------------------- *)

Lemma Typing_regularity : forall e A G R, Typing G e A R -> Typing G A a_Star R.
Proof.
  intros e A G R H1.
  induction H1; intros; eauto.
  - eapply binds_to_Typing; eauto.
  - apply invert_a_Pi in IHTyping1; eauto.
    destruct IHTyping1 as [h2 [[L h3] h4]].
    pick_fresh x.
    rewrite (tm_subst_tm_tm_intro x); auto.
    un_subst_tm.
    eapply Typing_tm_subst; eauto.
  - apply invert_a_Pi in IHTyping1; eauto.
    destruct IHTyping1 as [h2 [[L h3] h4]].
    pick_fresh x.
    rewrite (tm_subst_tm_tm_intro x); auto.
    un_subst_tm.
    eapply Typing_tm_subst; eauto.
  - apply invert_a_CPi in IHTyping; eauto using Typing_Ctx.
    destruct IHTyping as [h2 [[L h3] _]].
    pick_fresh c.
    rewrite (co_subst_co_tm_intro c); auto.
    un_subst_tm.
    eapply Typing_co_subst; eauto.
  - eapply Typing_weakening with (F:=nil)(G := nil) in H1.
    simpl_env in H1. eauto. auto. simpl_env. auto.
Qed.

(* --------------------------------------------------- *)

Lemma refl_iso: forall G D phi, PropWff G phi -> Iso G D phi phi.
Proof.
  intros G D phi H.
  destruct phi.
  inversion H.
  assert (Ctx G). eauto.
  assert (Typing G A a_Star R). { eapply Typing_regularity; eauto. }
  apply E_PropCong; eauto.
Qed.


Lemma sym_iso: forall G D phi1 phi2, Iso G D phi1 phi2 -> Iso G D phi2 phi1.
Proof.
  intros G D phi1 phi2 H.
  induction H.
  - assert (Ctx G). eauto.
    apply E_PropCong; apply E_Sym; auto.
  - eapply E_IsoConv; eauto.
  - eapply E_CPiFst; eauto.
Qed.

(* --------------------------------------------------- *)


Lemma invert_a_UAbs:
  forall G rho A R1 R b0,
    Typing G (a_UAbs rho R1 b0) A R
    -> exists A1 B1, DefEq G (dom G) A (a_Pi rho A1 R1 B1) a_Star R
               /\ (exists L, forall x, x `notin` L ->
                            Typing ([(x, Tm A1 R1)] ++ G)
                                   (open_tm_wrt_tm b0 (a_Var_f x))
                                   (open_tm_wrt_tm B1 (a_Var_f x)) R
                            /\ Typing ([(x, Tm A1 R1)] ++ G)
                                     (open_tm_wrt_tm B1 (a_Var_f x)) a_Star R
                            /\ RhoCheck rho x (open_tm_wrt_tm b0 (a_Var_f x)))
               /\ Typing G A1 a_Star R1.
Proof.
  intros G rho A R1 R b0.
  move e: (a_UAbs rho R1 b0) => t1.
  move => h0.
  induction h0; auto; try done.
  inversion e; subst.
  - destruct (IHh0 eq_refl) as (A1 & B1 & h1 & h2 & h3).
    exists A1, B1. repeat split; eauto 2. inversion h2 as [L h2'].
    exists L. intros. destruct (h2' x H1) as (h21 & h22 & h23).
    repeat split; try eapply E_SubRole; eauto.
  - exists A, B.
    split.
    + inversion e; subst. apply (E_Refl _ _ _ a_Star); auto.
      apply (E_Pi (L \u (dom G))); auto.
      intros x HH.
      apply (@Typing_regularity (open_tm_wrt_tm a (a_Var_f x))); auto.
    + inversion e; subst; clear e.
      split; auto.
      exists (L \u (dom G)).
      intros x HH.
      repeat split; auto.
      apply (@Typing_regularity (open_tm_wrt_tm a (a_Var_f x))); auto.
  -  destruct IHh0_1 as [A1 [B1 [h3 [L h2]]]]; auto.
     subst.
     exists A1, B1.
     split.
     + apply (@E_Trans _ _ _ _ _ _ A); auto.
     + split; auto.
Qed.


Lemma invert_a_UCAbs: forall G A R b0,
    Typing G (a_UCAbs b0) A R ->
    exists a b T R' B1 R'', PropWff G (Eq a b T R')
                /\ DefEq G (dom G) A (a_CPi (Eq a b T R') B1) a_Star R /\
                (exists L, forall c, c `notin` L ->
                           Typing ([(c, Co (Eq a b T R'))] ++ G)
                                  (open_tm_wrt_co b0 (g_Var_f c))
                                  (open_tm_wrt_co B1 (g_Var_f c)) R'' /\
                           Typing ([(c, Co (Eq a b T R'))] ++ G)
                                  (open_tm_wrt_co B1 (g_Var_f c)) a_Star R'')
                 /\ SubRole R'' R.
Proof.
  intros G A R b0.
  move e: (a_UCAbs b0) => t1.
  move => h0.
  induction h0; auto; try done.
  - destruct (IHh0 e) as 
    [a' [b' [T [R' [B2 [R'' [h3 [h4 [h5 h6]]]]]]]]].
    exists a', b', T, R', B2, R''. split; auto.
    split. eapply E_Sub; eauto. split. apply h5. eauto.
  - destruct IHh0_1 as
    [a' [b' [T [R' [B2 [R'' [h3 [h4 [[L h5] h6]]]]]]]]]; auto.
    exists a', b', T, R', B2, R''.
    split; auto.
    split.
    + apply (E_Trans _ _ _ _ _ _ A); auto.
    + split. exists L; auto. assumption.
  - induction phi.
    exists a0, b, A, R0, B, R.
    split; auto.
    split.
    + apply (E_Refl _ _ _ a_Star); auto.
      apply (E_CPi (L \u (dom G))); auto.
      intros c H2.
      apply (@Typing_regularity (open_tm_wrt_co a (g_Var_f c))); auto.
    + split. exists (L \u (dom G)).
      inversion e; subst; clear e.
      intros c H2.
      split; auto.
      apply (@Typing_regularity (open_tm_wrt_co a (g_Var_f c))); auto.
      auto.
Qed.


Lemma invert_a_App_Rel : forall G a b C R R',
    Typing G (a_App a Rel R b) C R' ->
    exists A B R'', Typing G a (a_Pi Rel A R B) R'' /\
           Typing G b A R /\
           DefEq G (dom G) C (open_tm_wrt_tm B b) a_Star R' /\ SubRole R'' R'.
Proof.
  intros G a b C R R'.
  move e : (a_App a Rel R b) => t1.
  move => h1.
  induction h1; auto; try done.
  - destruct (IHh1 e) as [A0 [B [R3 [h0 [h2 [h3 h4]]]]]].
    exists A0, B, R3. repeat split; eauto 3.
  - exists A, B, R'. inversion e; subst.
    assert (h2 : Typing G (open_tm_wrt_tm B a0) a_Star R').
    + (have: Typing G (a_Pi Rel A R0 B) a_Star R' by apply (Typing_regularity h1_1)) => h3.
      destruct (invert_a_Pi h3) as [_ [[L h4] h5]].
      pick fresh x.
      rewrite (tm_subst_tm_tm_intro x); auto.
      replace a_Star with (tm_subst_tm_tm a0 x a_Star); auto.
      apply Typing_tm_subst with (A := A) (R := R0); auto.
    + repeat split; auto.
  - destruct (IHh1_1 e) as [A0 [B0 [R1 [h3 [h2 [e2 s]]]]]].
    exists A0, B0, R1.
    repeat split; auto.
    apply (E_Trans _ _ _ _ _ _ A); auto.
Qed.


Lemma invert_a_App_Irrel : forall G a b C R R',
    Typing G (a_App a Irrel R b) C R' ->
    exists A B b0 R'', Typing G a (a_Pi Irrel A R B) R'' /\
              Typing G b0 A R /\
              DefEq G (dom G) C (open_tm_wrt_tm B b0) a_Star R' /\ SubRole R'' R'.
Proof.
  intros G a b C R R'.
  move e : (a_App a Irrel R b) => t1.
  move => h1.
  induction h1; auto; try done.
  - destruct (IHh1 e) as [A0 [B [b0 [R3 [h0 [h2 [h3 h4]]]]]]].
    exists A0, B, b0, R3. repeat split; eauto 3.
  - exists A, B, a0, R'. inversion e; subst.
    assert (h2 : Typing G (open_tm_wrt_tm B a0) a_Star R').
    + (have: Typing G (a_Pi Irrel A R0 B) a_Star R' by apply (Typing_regularity h1_1)) => h3.
      destruct (invert_a_Pi h3) as [_ [[L h4] h5]].
      pick fresh x.
      rewrite (tm_subst_tm_tm_intro x); auto.
      replace a_Star with (tm_subst_tm_tm a0 x a_Star); auto.
      apply Typing_tm_subst with (A := A) (R := R0); auto.
    + repeat split; auto.
  - destruct (IHh1_1 e) as [A0 [B0 [b0 [R1 [h3 [h2 [h4 s]]]]]]].
    exists A0, B0, b0, R1.
    repeat split; auto.
    apply (E_Trans _ _ _ _ _ _ A); auto.
Qed.

Lemma invert_a_CApp : forall G a g A R,
    Typing G (a_CApp a g) A R ->
    g = g_Triv /\
    exists a1 b1 A1 R1 B R2, Typing G a (a_CPi (Eq a1 b1 A1 R1) B) R2 /\
             DefEq G (dom G) a1 b1 A1 R1 /\
             DefEq G (dom G) A (open_tm_wrt_co B g_Triv) a_Star R /\
             SubRole R2 R.
Proof.
  intros G a g A R H.
  dependent induction H.
  - destruct (IHTyping a g eq_refl) as (p & a1 & b1 & A1 & R3 & BB & R4 & Ta & Dab & DAB & s).
    split; auto. exists a1, b1, A1, R3, BB, R4. repeat split; auto.
    eapply E_Sub; eauto. eauto.
  - destruct (IHTyping1 a g eq_refl) as (p & a1 & b1 & A1 & R3 & BB & R4 & Ta & Dab & DAB & s).
    split; first by done.
    exists a1, b1, A1, R3, BB, R4.
    repeat split; auto.
    apply E_Trans with (a1 := A); auto.
  - split; first by done.
    exists a0, b, A, R, B1, R'.
    repeat split; auto.
    eapply E_Refl.
    have CTX: Ctx G by eauto.
    have TC: Typing G (a_CPi (Eq a0 b A R) B1) a_Star R'. eapply Typing_regularity; eauto.
    destruct (invert_a_CPi TC) as [_ [[L h4] h5]].
    pick fresh x.
    move: (h4 x ltac:(auto)) => h6.
    eapply Typing_co_subst  in h6. simpl in h6.
    rewrite (co_subst_co_tm_intro x); eauto.
    simpl; eauto.
Qed.

Lemma max1 : forall R1 R2, SubRole R1 (max R1 R2).
intros. destruct R1; destruct R2; simpl; auto.
Qed.
Lemma max2 : forall R1 R2, SubRole R2 (max R1 R2).
intros. destruct R1; destruct R2; simpl; auto.
Qed.

Lemma max_cov1 : forall R1 R2 R3, SubRole R2 R3 -> SubRole (max R2 R1) (max R3 R1).
intros R1 R2 R3 H. destruct R1; destruct R2; destruct R3; simpl; auto.
Qed.

Lemma max_cov2 : forall R1 R2 R3, SubRole R2 R3 -> SubRole (max R1 R2) (max R1 R3).
intros R1 R2 R3 H. destruct R1; destruct R2; destruct R3; simpl; auto.
Qed.


Lemma invert_a_Conv2
     : ∀ (G : context) (a A : tm) (R1 R2 : role),
       Typing G (a_Conv a R1 g_Triv) A R2
       → ∃ (B : tm),
         Typing G a B R2 ∧ DefEq G (dom G) A B a_Star R1.
Proof.
  intros G a A R1 R2 H. dependent induction H.
  - edestruct IHTyping as (B0 & h); eauto. split_hyp.
    exists B0. repeat split; auto.
    eapply E_SubRole; eauto. 
    eapply E_Sub; eauto using max2. 
    apply max_cov1; auto.
  - edestruct IHTyping1 as (B0 & h); eauto. split_hyp.
    exists B0. repeat split; auto.
    eapply E_Trans with (a1 := A). eapply E_Sym. 
    eapply E_Sub; eauto using max1.  auto.
  - exists A1. 
    repeat split; auto.
Qed.

(*
Lemma invert_a_Conv : forall G a A R1 R2,
     Typing G (a_Conv a R1 g_Triv) A R2 ->
      exists B R3 R4, Typing G a B R3 /\ DefEq G (dom G) A B a_Star R4 /\
            SubRole R3 R2.
Proof. intros. dependent induction H.
        - destruct (IHTyping _ _ eq_refl) as [B [R3 [R4 [H1 [H2 H3]]]]].
          exists B, R3, R4. repeat split; auto. apply Trans with R0; auto.
        - destruct (IHTyping1 _ _ eq_refl) as [C [R3 [R4 [H' [H2 H3]]]]].
          exists C, R3, Rep. repeat split; auto. apply E_Sym in H0.
          apply E_Trans with (a1 := A); eapply E_Sub; eauto.
          destruct R; auto. destruct R4; auto.
        - exists A1, R0, R1. repeat split; auto.
Qed.
*)

(* --------------------------------------------------- *)

Inductive context_DefEq : available_props -> context -> context -> Prop :=
| Nul_Eqcontext: forall D, context_DefEq D nil nil
| Factor_Eqcontext_tm: forall G1 G2 D A A' R x,
    context_DefEq D G1 G2 ->
    DefEq G1 D A A' a_Star R ->
    DefEq G2 D A A' a_Star R ->
    context_DefEq D ([(x, Tm A R)] ++ G1) ([(x, Tm A' R)] ++ G2)
| Factor_Eqcontext_co: forall D G1 G2 Phi1 Phi2 c,
    context_DefEq D G1 G2 ->
    Iso G1 D Phi1 Phi2 ->
    Iso G2 D Phi1 Phi2 ->
    context_DefEq D ([(c, Co Phi1)] ++ G1) ([(c, Co Phi2)] ++ G2).

Hint Constructors context_DefEq.

Lemma context_tm_binding_defeq: forall D (G1 G2: context) A R x,
    Ctx G1 -> Ctx G2 -> context_DefEq D G1 G2 ->
    binds x (Tm A R) G1 -> exists A', (binds x (Tm A' R) G2) /\ DefEq G2 D A A' a_Star R.
Proof.
  intros D G1 G2 A R x H1 h0 H H0.
  induction H; try done.
  - case H0; simpl.
    + intros M4.
      exists A'.
      * split; auto.
         -- left.
            inversion M4; auto.
         -- inversion M4; subst; clear M4.
            rewrite_env (nil ++ [(x, Tm A' R)] ++ G2).
            pose K := DefEq_weakening.
            inversion h0; subst.
            inversion H1; subst.
            eapply K with (G0 := G2).
            all: eauto.
    + intros M4.
      case IHcontext_DefEq; auto; try done.
      * by inversion H1.
      * by inversion h0.
      * intros A2 [h1 h2].
         exists A2.
         split; auto.
         rewrite_env (nil ++ [(x0, Tm A' R0)] ++ G2).
         pose K := DefEq_weakening.
         eapply K; eauto.
  - case H0; try done; simpl.
    move => h1.
    case IHcontext_DefEq; auto.
    + by inversion H1.
    + by inversion h0.
    + intros A2 [h2 h3].
       exists A2.
       split; auto.
       rewrite_env (nil ++ [(c, Co Phi2)] ++ G2).
       pose K := DefEq_weakening.
       eapply K; eauto.
Qed.

Lemma context_co_binding_defeq:
  forall D (G1 G2: context) phi1 c,
    Ctx G1 ->
    Ctx G2 -> context_DefEq D G1 G2 ->
    binds c (Co phi1) G1 ->
    exists phi2, (binds c (Co phi2) G2) /\ Iso G2 D phi1 phi2.
Proof.
  intros G1 G2 phi1 c m H Hip H0 H1.
  induction H0; auto; try done.
  - case H1; move => h0.
    inversion h0.
    destruct IHcontext_DefEq as [phi2 [h1 h2 ]]; auto.
    + inversion H; auto.
    + by inversion Hip.
    + exists phi2.
      split.
      * right; auto.
      * eapply Iso_weakening with (F := nil); eauto.
  - case H1; move => h0.
    + inversion h0; subst; clear h0.
      exists Phi2.
      split.
      * auto.
      * eapply Iso_weakening with (F:=nil) (G0 := G2); eauto.
    + destruct IHcontext_DefEq as [phi2 [h1 h2]]; auto.
      * inversion H; auto.
      * by inversion Hip.
      * exists phi2.
        split; auto.
        eapply Iso_weakening with (F:=nil); eauto.
Qed.


Lemma context_DefEq_sub :
  forall D G1 G2, context_DefEq D G1 G2 -> forall D', D [<=] D' -> context_DefEq D' G1 G2.
Proof.
  induction 1.
  eauto.
  intros D' Sub.
  pose K := (fourth weaken_available_mutual _ _ _ _ _ _ _ D' Sub). clearbody K.
  econstructor; eauto.
  intros D' Sub.
  pose K := (third weaken_available_mutual _ _ _ _ _ D' Sub). clearbody K.
  eauto.
Qed.

Lemma same_dom : forall D (G1 : context) G2,
    context_DefEq D G1 G2 -> (@dom ett_ott.sort G1) = (@dom ett_ott.sort G2).
Proof.
  induction 1; auto.
  simpl. rewrite IHcontext_DefEq. auto.
  simpl. rewrite IHcontext_DefEq. auto.
Qed.


Lemma context_DefEq_weaken_available :
  forall D G1 G2, context_DefEq D G1 G2 -> context_DefEq (dom G1) G1 G2.
Proof.
  induction 1.
  eauto.
  assert (SUB : (dom G1) [<=] (dom ([(x,Tm A R)] ++ G1))). simpl. fsetdec.
  econstructor; auto.
  apply (context_DefEq_sub IHcontext_DefEq SUB).
  eapply (fourth weaken_available_mutual G1).
  eapply DefEq_weaken_available. eauto. auto.
  eapply (fourth weaken_available_mutual G2).
  eapply DefEq_weaken_available. eauto.
  erewrite <- (@same_dom _ G1 G2). auto. eauto.
  assert (SUB : (dom G1) [<=] (dom ([(c,Co Phi1)] ++ G1))). simpl. fsetdec.
  econstructor; auto.
  apply (context_DefEq_sub IHcontext_DefEq SUB).
  eapply (third weaken_available_mutual G1).
  eapply Iso_weaken_available. eauto. auto.
  eapply (third weaken_available_mutual G2).
  eapply Iso_weaken_available. eauto.
  erewrite <- (@same_dom _ G1 G2). auto. eauto.
Qed.


Lemma context_DefEq_mutual:
  (forall G1  a A R,   Typing G1 a A R -> forall D G2,
        Ctx G2 -> context_DefEq D G1 G2 -> Typing G2 a A R) /\
  (forall G1  phi,   PropWff G1 phi -> forall D G2,
        Ctx G2 -> context_DefEq D G1 G2 -> PropWff G2 phi) /\
  (forall G1 D p1 p2, Iso G1 D p1 p2 ->
                  forall G2, Ctx G2 -> context_DefEq D G1 G2 -> Iso G2 D p1 p2) /\
  (forall G1 D1 A B T R,   DefEq G1 D1 A B T R -> forall G2, Ctx G2 -> context_DefEq D1 G1 G2 ->
                                          DefEq G2 D1 A B T R) /\
  (forall G1 ,       Ctx G1 -> forall G2 D x A R, Ctx G2 -> context_DefEq D G1 G2
                                   -> binds x (Tm A R) G1 -> Typing G2 A a_Star R).
Proof.
  (* apply typing_wff_iso_defeq_mutual; *)
  ext_induction con; 
  eauto 3; try done.
  - intros G1 x A R c H b D G2 H0 H1.
    case (@context_tm_binding_defeq D G1 G2 A R x); auto.
    intros A2 [h0 h1].
    apply (E_Conv _ _ _ _ A2); auto.
    eapply DefEq_weaken_available; eauto.
    eapply H; eauto.
  - intros L G1 rho A R B R' t H t0 S D G2 H1 H2.
    apply (E_Pi (L \u (dom G2))); auto.
    intros x H3.
    eapply H; auto.
    eapply E_ConsTm; eauto.
    apply Factor_Eqcontext_tm; eauto 2.
    eapply E_Refl; eauto.
    eapply S; eauto.
  - intros L G1 rho A a R B R' t H t0 r S D G2 H1 H2.
    apply (E_Abs (L \u (dom G2))); auto.
    intros x H3.
    eapply H; auto.
    eapply E_ConsTm; eauto.
    eapply Factor_Eqcontext_tm; eauto 3.
    eapply r; eauto.
  - intros. eauto 4.
  - intros. eauto 4.
  - intros G a B R A t H d H0 d0 t0 D G2 H1 H2.
    apply (E_Conv _ _ _ _ A); auto. eapply H; eauto.
    rewrite <- (same_dom H2).
    eapply H0; eauto.
    eapply context_DefEq_weaken_available. eauto.
    eapply t0; eauto.
  - intros L G1 phi B R t H p H0 D G2 H1 H2.
    apply (E_CPi (L \u (dom G2))); eauto.
    intros c H3.
    eapply H; eauto.
    apply Factor_Eqcontext_co; eauto 2.
    eapply refl_iso; auto.
    eapply refl_iso; auto.
    eauto.
  - intros L G1 phi a B R t H p H0 D G2 H1 H2.
    apply (E_CAbs (L \u (dom G2))); auto.
    intros c H3.
    eapply H; eauto.
    eapply Factor_Eqcontext_co; eauto 2.
    eapply refl_iso; eauto.
    eapply refl_iso; eauto.
    eauto.
  - intros G a1 B1 R' a b A R t H d H0 D G2 H1 H2.
    apply (E_CApp _ _ _ _ a b A R); auto. eauto.
    rewrite <- (same_dom H2).
    eapply H0. auto.
    eapply context_DefEq_weaken_available. eauto.
  - intros. eapply con; eauto 2.
    eapply DefEq_weaken_available. 
    apply H0; eauto.
    eapply context_DefEq_weaken_available; eauto.
  - intros G a b A R t H t0 H0 t1 H1 D G2 H2 H3.
    apply E_Wff; eauto.
  - intros. eauto 4.
  - intros G D A1 A2 A R B d H p H0 p0 H1 G2 H2 H3.
    eapply E_IsoConv; eauto.
  - intros G D a b A R c c0 H b0 i G2 H0 H1.
    case (@context_co_binding_defeq D G G2 (Eq a b A R) c); auto.
    intros phi' [h0 h1].
    destruct phi' as [A' B'].
    eapply (E_Assn _ D) in h0; auto.
    eapply sym_iso in h1. 
    eapply E_Cast; eauto.
  - intros. eauto 4.
  - intros. eauto 4.
  - intros L. intros.
    pick fresh x and apply E_PiCong; eauto 2.
    eapply H0; eauto.
  - intros.
    pick fresh x and apply E_AbsCong; eauto 2.
    eapply H; eauto.
  - intros. eauto 4.
  - intros. eauto 4.
  - intros. eauto 4.
  - intros.
    pick fresh x and apply E_CPiCong; eauto 2.
    eapply H0; eauto. inversion p; subst.
    econstructor. auto.
    econstructor; eapply E_Refl; auto.
    pose (Q := H1 D G2 H4 H5). inversion Q; subst.
    econstructor; eapply E_Refl; auto.
  - intros.
    pick fresh c and apply E_CAbsCong; eauto 2.
    destruct phi1.
    eapply H; eauto.
    econstructor; eauto using refl_iso.
  - intros G D a1 b1 B R' a b A R d H d0 H0 G2 H1 H2.
    eapply E_CAppCong; eauto 2.
    rewrite <- (same_dom H2).
    apply H0; eauto.
    eapply context_DefEq_weaken_available. eauto.
  - intros G D B1 B2 R0 a1 a2 A R a1' a2' A' R' d H d0 H0 d1 H1 G2 H2 H3.
    eapply E_CPiSnd; eauto 2. eapply DefEq_weaken_available.
    eapply H0; eauto 2.
    eapply context_DefEq_weaken_available. eauto 2.
    eapply DefEq_weaken_available; eauto 2.
    eapply H1; eauto 2.
    eapply context_DefEq_weaken_available; eauto 2.
  - intros. eauto 4.
  - intros G D a b B R2 A R1 d H d0 H0 S G2 H1 H2.
    apply (E_EqConv _ _ _ _ _ _ A R1); auto.
    rewrite <- (same_dom H2).
    apply H0; auto.
    eapply context_DefEq_weaken_available; eauto.
  - intros. eapply con. eauto. eapply DefEq_weaken_available.
    eapply H0. eauto. eapply context_DefEq_weaken_available; eauto.
    eauto.
  - intros G x A R c H t H0 n G2 D x0 A0 R' H1 H2 H3.
    inversion H3; subst.
    + inversion H4; subst.
      inversion H2; subst.
      have: Typing G0 A0 a_Star R'; auto.
      * eapply H0; eauto.
      * move => h0.
        pose K := Typing_weakening.
        rewrite_env (nil ++ [(x0, Tm A' R')] ++ G0).
        apply (K _ _ _ _ h0); auto.
    + inversion H2; subst.
      have: Typing G0 A0 a_Star R'; auto.
      * apply (H _ D x0); auto.
          by inversion H1; auto.
      * move => h0.
        pose K := Typing_weakening.
        rewrite_env (nil ++ [(x, Tm A' R)] ++ G0).
        apply (K _ _ _ _ h0); auto.
  - intros G c phi c0 H p H0 n G2 D x A R H1 H2 H3.
    inversion H3; try done.
    inversion H2; subst.
    have: Typing G0 A a_Star R.
    + apply (H _ D x); auto.
        by inversion H1.
    + move => h0.
      pose K := Typing_weakening.
      rewrite_env (nil ++ [(c, Co Phi2) ] ++ G0).
      apply (K _ _ _ _ h0); auto.
Qed.

Lemma context_DefEq_typing:
  forall G1  a A R,
    Typing G1 a A R -> forall D G2, Ctx G2 -> context_DefEq D G1 G2 -> Typing G2 a A R.
Proof.
  apply context_DefEq_mutual.
Qed.


Lemma refl_context_defeq: forall G D, Ctx G -> context_DefEq D G G.
Proof.
  move => G; induction G.
  - intros D H.
    eapply Nul_Eqcontext.
  - intros D H. destruct a.
    inversion H; subst.
    + apply Factor_Eqcontext_tm; eauto.
    + apply Factor_Eqcontext_co; eauto 2.
      eapply refl_iso; done.
      eapply refl_iso; done.
Qed.


Lemma DefEqIso_regularity :
  (forall G0 a A R, Typing G0 a A R -> True ) /\
  (forall G0 phi,  PropWff G0 phi -> True ) /\
  (forall G D p1 p2, Iso G D p1 p2 ->
                 PropWff G p1 /\ PropWff G p2) /\
  (forall G D A B T R,   DefEq G D A B T R ->
                  Typing G A T R /\ Typing G B T R) /\
  (forall G0, Ctx G0 -> True).
Proof.
  ext_induction con; eauto; try done.
  - intros G D A1 B1 A R A2 B2 d H d0 H0.
    split_hyp.
    split; apply E_Wff; solve [auto | eapply Typing_regularity; eauto].
  - intros.
    split_hyp.
    have CTX: Ctx G by eauto.
    split; solve [eapply invert_a_CPi; eauto].
  - intros G D a0 b0 A R c c0 H b i.
    apply binds_to_PropWff in b; auto.
    inversion b; subst.
    split; auto.
  -  intros G D a b A R d H.
    split_hyp; auto.
  - intros G D a b A R a1 H1 H hi0 hi1.
    destruct H as [h0 h1]; auto.
    split_hyp; auto.
  - intros G D a b A R2 R1 d [T1 T2] S.
    split; eapply E_SubRole; eauto.
  - intros L G D rho R b1 b2 A2 B R' d H0 t H1 r1 r2.
    split_hyp.
    repeat split; auto.
    + apply (E_Abs (L \u (dom G))); eauto.
      intros x H4.
      apply H0; auto.
    + (have: Ctx G by eauto) => CTX.
      apply (E_Conv _ _ _ _ ((a_Pi rho A2 R B))); auto.
      -- apply (E_Abs (L \u dom G)); eauto.
         intros x H4.
         eapply (@context_DefEq_typing ([(x, Tm A2 R)] ++ G)); eauto.
         apply H0; auto.
         apply Factor_Eqcontext_tm; eauto.
         apply refl_context_defeq; auto.
      -- apply (E_PiCong (L \u (dom G))); auto.
         ++ intros x H4.
            apply E_Refl; eauto.
            eapply (@context_DefEq_typing ([(x, Tm A2 R)] ++ G)); eauto.
            eapply Typing_regularity; eauto 2.
            apply H0; auto.
            apply Factor_Eqcontext_tm; eauto.
            apply refl_context_defeq; auto.
         ++ apply (E_Pi (L \u (dom G))); eauto.
            intros x H4.
            have: x `notin` L; auto => h0.
            destruct (H0 x h0).
            eapply Typing_regularity. eauto 2.
         ++ apply (E_Pi (L \u (dom G))); eauto.
            intros x H4.
            eapply Typing_regularity; eauto 2.
            apply H0; eauto.
      -- apply (E_Pi (L \u (dom G))); eauto.
         intros x H4.
         eapply Typing_regularity; eauto 2.
         apply H0; eauto.
  - intros G D a1 R a2 b1 b2 B R' A d H d0 H0.
    split_hyp.
    (have: Ctx G by eauto) => CTX.
    split; eauto.
    apply (E_Conv _ _ _ _ (open_tm_wrt_tm B b2)); auto.
    eapply (E_App); eauto.
    apply (E_PiSnd _ _ _ _ _ _ _ Rel A R A); auto.
    apply E_Refl; auto.
    eapply Typing_regularity; eauto.
    apply E_Sym.
    eapply DefEq_weaken_available. destruct R; eauto.
    apply Typing_regularity in H; auto.
    apply invert_a_Pi in H; eauto.
    destruct H as [_ [[L h0] _]].
    pick_fresh x.
    have: x `notin` L; auto => h1.
    pose K := Typing_tm_subst (h0 x h1) H0.
    clearbody K.
    repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in K; try solve [apply (Typing_lc H0); eauto].
    simpl in K.
    destruct eq_dec; try congruence.
    rewrite tm_subst_tm_tm_fresh_eq in K; auto.
  - intros G D A1 A2 B1 B2 R' d R H h0 h1 _.
    split_hyp.
    (have: Ctx G by eauto) => CTX.
    split; eauto.
  - intros G D A1 A2 R rho B1 B2 R' d H. 
    split_hyp.
    (have: Ctx G by eauto) => CTX.
    apply E_PiFst in d.
    apply invert_a_Pi in H; eauto.
    apply invert_a_Pi in H0; eauto.
    split_hyp; auto.
  - intros G D B1 a1 B2 a2 R' rho A1 R A2 d H d0 H0.
    split_hyp.
    (have: Ctx G by eauto) => CTX.
    repeat split.
    + apply invert_a_Pi in H; eauto.
      destruct H as [_ [[L h0] _]].
      pick_fresh x.
      have: x `notin` L; auto => h1.
      pose K := Typing_tm_subst (h0 x h1) H0.
      clearbody K.
      repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in K; try solve [apply (Typing_lc H0); eauto].
      simpl in K.
      destruct eq_dec; try congruence.
      rewrite tm_subst_tm_tm_fresh_eq in K; auto.
    + apply invert_a_Pi in H2; eauto.
      destruct H2 as [_ [[L h0] hi]].
      pick_fresh x.
      have: x `notin` L; auto => h1.
      apply (E_Conv _ _ A2) in H1; auto.
      pose K := Typing_tm_subst (h0 x h1) H1.
      clearbody K.
      repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in K; try solve [apply (Typing_lc H1); eauto].
      simpl in K.
      destruct eq_dec; try congruence.
      rewrite tm_subst_tm_tm_fresh_eq in K; auto.
      apply E_PiFst in d; auto.
      eapply DefEq_weaken_available; eauto.
  - intros L G D a b phi1 B R d H p H0.
    split_hyp.
    have CTX: Ctx G by eauto.
    repeat split; eauto.
    + apply (E_CAbs (L \u (dom G))); eauto.
      intros c H3.
      apply H; eauto.
    + apply (E_Conv _ _ _ _ ((a_CPi phi1 B))); auto.
      * apply (E_CAbs (L \u (dom G))); eauto.
        intros c H3.
        eapply (@context_DefEq_typing ([(c, Co phi1)] ++ G)); eauto.
        apply H; eauto.
        apply Factor_Eqcontext_co; eauto 2.
        apply refl_context_defeq; eauto.
        all: apply refl_iso; eauto.
      * destruct phi1. apply (E_CPiCong (L \u (dom G))); auto.
        -- apply refl_iso; auto.
        -- intros c H3.
           apply E_Refl; eauto.
           eapply (@context_DefEq_typing ([(c, Co (Eq a0 b0 A R0))] ++ G)); eauto.
           eapply Typing_regularity; eauto 2.
           apply H; eauto 4.
           apply Factor_Eqcontext_co; eauto 4.
           apply refl_context_defeq; eauto 4.
           all: apply refl_iso; eauto 4.
        -- apply (E_CPi (L \u dom G)); eauto.
           intros c H3.
           eapply (@context_DefEq_typing ([(c, Co (Eq a0 b0 A R0))] ++ G)); eauto.
           eapply Typing_regularity; eauto 2.
           apply H; eauto.
           apply Factor_Eqcontext_co; eauto 4.
           apply refl_context_defeq; eauto 4.
           all: apply refl_iso; eauto.
        -- apply (E_CPi (L \u dom G)); eauto.
           intros c H3.
           eapply Typing_regularity; eauto 2.
           apply H; auto.
      * apply (E_CPi (L \u (dom G))); eauto.
        intros c H3.
        destruct (H c); auto.
        eapply Typing_regularity; eauto.
  - intros L G D phi1 a R' phi2 b B R i H d H0.
    split_hyp.
    split.
    eapply E_CApp; eauto.
    eapply E_CApp; eauto.
  - intros G D B1 B2 R0 a1 a2 A R a1' a2' A' R' d H d0 H0 d1 H1.
    split_hyp.
    (have: Ctx G by eauto) => CTX.
    apply invert_a_CPi in H; auto.
    apply invert_a_CPi in H4; auto.
    destruct H as [_ [[L0 ty0] _]].
    destruct H4 as [_ [[L1 ty1] _]].
    pick_fresh c.
    repeat split; eauto.
    + have: c `notin` L0; auto => h0.
      pose K := Typing_co_subst (ty0 c h0) d0.
      clearbody K.
      repeat rewrite co_subst_co_tm_open_tm_wrt_co in K; auto.
      simpl in K.
      destruct eq_dec; try congruence.
      rewrite co_subst_co_tm_fresh_eq in K; auto.
    + have: c `notin` L1; auto => h0.
      pose K := Typing_co_subst (ty1 c h0) d1.
      clearbody K.
      repeat rewrite co_subst_co_tm_open_tm_wrt_co in K; auto.
      simpl in K.
      destruct eq_dec; try congruence.
      rewrite co_subst_co_tm_fresh_eq in K; auto.
  - intros G. intros.
    split_hyp.
    inversion H1; subst.
    (have: Ctx G by eauto) => h0.
    eauto.
  - intros G D a b B R2 A R1 d H d0 H0 S.
    split_hyp; auto.
    split; eapply E_Conv; eauto.
  - intros G D A A' a b R a' b' i H.
    split_hyp; eauto.
    inversion H0; subst.
    inversion H; subst.
    split; auto.
    Unshelve. exact (dom G). exact (dom G).
    auto. auto. auto.
  - intros.
    pcess_hyps.
    split;
    eapply E_TyCast; eauto 3 using DefEq_weaken_available.
Qed.

Lemma DefEq_regularity :
  forall G D A B T R, DefEq G D A B T R -> PropWff G (Eq A B T R).
Proof.
  intros G D A B T R H.
  apply DefEqIso_regularity in H.
  split_hyp.
  apply E_Wff; auto.
  eapply Typing_regularity; eauto.
Qed.

Lemma Iso_regularity :
  forall G D phi1 phi2, Iso G D phi1 phi2 -> PropWff G phi1 /\ PropWff G phi2.
Proof.
  intros G D phi1 phi2 H.
  eapply (third DefEqIso_regularity); eauto.
Qed.


Lemma PropWff_regularity :
  forall G A B T R, PropWff G (Eq A B T R) ->  Typing G A T R /\ Typing  G B T R.
Proof.
  intros G A B T R H.
  inversion H; subst.
  repeat split; auto.
Qed.

(* -------------------------------------------------------------- *)

Lemma DefEq_conv : forall G D a b A B R, DefEq G D a b A R -> 
                  DefEq G (dom G) A B a_Star R -> DefEq G D a b B R.
Proof.
  intros. eauto.
Qed.


Lemma trans_iso : forall G D a0 b0 A a1 b1 B a2 b2 C R,
    Iso G D (Eq a0 b0 A R) (Eq a1 b1 B R) -> 
    Iso G D (Eq a1 b1 B R) (Eq a2 b2 C R) -> 
    Iso G D (Eq a0 b0 A R) (Eq a2 b2 C R).
Proof.
  intros G D a0 b0 A a1 b1 B a2 b2 C R H1 H2.
  destruct (Iso_regularity H1) as (WFF1 & WFF2).
  inversion WFF1. inversion WFF2. subst.
  destruct (Iso_regularity H2) as (WFF3 & WFF4).
  inversion WFF3. inversion WFF4. subst.

  have CTX: Ctx G by eauto 2.

  have DE1: DefEq G D (a_CPi (Eq a0 b0 A R) a_Star) (a_CPi (Eq a1 b1 B R) a_Star) a_Star R.
  { pick fresh x and apply E_CPiCong; eauto 2.
    unfold open_tm_wrt_co. simpl.
    constructor. constructor. constructor; auto.

    pick fresh x and apply E_CPi; eauto 2.
    unfold open_tm_wrt_co. simpl.
    constructor. constructor; auto.

    pick fresh x and apply E_CPi; eauto 2.
    unfold open_tm_wrt_co. simpl.
    constructor. constructor; auto.
  }

  have DE2: DefEq G D (a_CPi (Eq a1 b1 B R) a_Star) (a_CPi (Eq a2 b2 C R) a_Star) a_Star R.
  { pick fresh x and apply E_CPiCong; eauto 2.
    unfold open_tm_wrt_co. simpl.
    constructor. constructor. constructor; auto.

    pick fresh x and apply E_CPi; eauto 2.
    unfold open_tm_wrt_co. simpl.
    constructor. constructor; auto.

    pick fresh x and apply E_CPi; eauto 2.
    unfold open_tm_wrt_co. simpl.
    constructor. constructor; auto.
  }

  move: (E_Trans _ _ _ _ _ _ _ DE1 DE2) => DE3.

  eapply E_CPiFst. eauto.
Qed.

Lemma iso_cong : forall G D A A' B B' T T' R, 
                 DefEq G D A A' T R -> DefEq G D B B' T R -> 
                 DefEq G D T T' a_Star R -> Iso G D (Eq A B T R) (Eq A' B' T' R).
    Proof.
      intros.
      move: (DefEq_regularity H) => p0. inversion p0.
      move: (DefEq_regularity H0) => p1. inversion p1.
      move: (DefEq_regularity H1) => p2. inversion p2.
      subst.
      have AT: Typing G A T' R.
      eapply E_Conv; eauto using DefEq_weaken_available.
      have AT': Typing G A' T' R.
      eapply E_Conv; eauto using DefEq_weaken_available.
      have BT: Typing G B T' R.
      eapply E_Conv; eauto using DefEq_weaken_available.
      have BT': Typing G B' T' R.
      eapply E_Conv; eauto using DefEq_weaken_available.
      have IA: Iso G D (Eq A A' T R) (Eq A A' T' R).
      eapply E_IsoConv; eauto 2.
      have IB: Iso G D (Eq B B' T R) (Eq B B' T' R).
      eapply E_IsoConv; eauto 2.
      eapply trans_iso with (a1 := A) (b1 := B) (B := T').
      eapply E_IsoConv; eauto.
      eapply E_PropCong; eauto 2.
    Qed.


(* ----------------------------------------------------------------------------- *)

Lemma E_PiCong2 :  ∀ (L : atoms) (G : context) (D : available_props) rho (A1 B1 A2 B2 : tm) R R',
    DefEq G D A1 A2 a_Star R
    → (∀ x : atom,
          x `notin` L
          → DefEq ([(x, Tm A1 R)] ++ G) D (open_tm_wrt_tm B1 (a_Var_f x))
                  (open_tm_wrt_tm B2 (a_Var_f x)) a_Star R')
    → DefEq G D (a_Pi rho A1 R B1) (a_Pi rho A2 R B2) a_Star R'.
Proof.
  intros.
  move: (DefEq_regularity H) => WFF.
  inversion WFF. subst.
  assert (Typing G A1 a_Star R). eauto 1.
  assert (Typing G (a_Pi rho A1 R B1) a_Star R').
  {  eapply (E_Pi L); eauto 1. intros x Fr.
     move: (DefEq_regularity (H0 x Fr)) => WFF2.
     inversion WFF2. subst. eauto 1. }
  assert (Typing G (a_Pi rho A2 R B2) a_Star R').
  {
     eapply (E_Pi L); eauto 1. intros x Fr.
     move: (DefEq_regularity (H0 x Fr)) => WFF2.
     inversion WFF2. subst.
     have CTX: Ctx (x ~ Tm A1 R ++ G) by eauto.
     inversion CTX. subst.
     eapply context_DefEq_typing; eauto 1.
     eapply E_ConsTm; eauto 1.
     econstructor; eauto 1.
     apply refl_context_defeq. eauto 1. }
  eapply E_PiCong; eauto 1.
Qed.

Lemma E_CPiCong2  : ∀ (L : atoms) (G : context) (D : available_props) a0 b0 T0
                      (A : tm) a1 b1 T1 (B : tm) R R',
    Iso G D (Eq a0 b0 T0 R) (Eq a1 b1 T1 R)
    → (∀ c : atom,
          c `notin` L
              → DefEq ([(c, Co (Eq a0 b0 T0 R))] ++ G) D (open_tm_wrt_co A (g_Var_f c))
                      (open_tm_wrt_co B (g_Var_f c)) a_Star R')
    → DefEq G D (a_CPi (Eq a0 b0 T0 R) A) (a_CPi (Eq a1 b1 T1 R) B) a_Star R'.
Proof.
  intros.
  move: (Iso_regularity H) => [h0 h1].
  inversion h0. inversion h1. subst.
  assert (Typing G (a_CPi (Eq a0 b0 T0 R) A) a_Star R').
  { eapply (E_CPi L); eauto 1. intros x Fr.
    move: (DefEq_regularity (H0 x Fr)) => WFF2.
    inversion WFF2. subst. eauto 1. }
  assert (Typing G (a_CPi (Eq a1 b1 T1 R) B) a_Star R').
  { eapply (E_CPi L); eauto 1. intros x Fr.
    move: (DefEq_regularity (H0 x Fr)) => WFF2.
    inversion WFF2. subst.
    have CTX: Ctx (x ~ Co (Eq a0 b0 T0 R) ++ G) by eauto.
    inversion CTX. subst.
    eapply context_DefEq_typing; eauto 1.
    econstructor; eauto 1.
    econstructor; eauto 1.
     apply refl_context_defeq. eauto 1.
  }
  eapply E_CPiCong; eauto 1.
Qed.


(* Could also be an exists form *)
Lemma E_Pi2 : forall L G rho A B R R',
    (∀ x : atom, x `notin` L → Typing ([(x, Tm A R)] ++ G) (open_tm_wrt_tm B (a_Var_f x)) a_Star R') ->
    Typing G (a_Pi rho A R B) a_Star R'.
Proof.
  intros.
  eapply E_Pi; eauto.
  pick fresh x.
  move: (H x ltac:(auto)) => h0.
  have h1: Ctx (x ~ Tm A R ++ G) by eauto.
  inversion h1. auto.
Qed.

Lemma E_Abs2 : ∀ (L : atoms) (G : context) (rho : relflag) (a A B : tm) R R',
    (∀ x : atom,
        x `notin` L → Typing ([(x, Tm A R)] ++ G) (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x)) R')
    → (∀ x : atom, x `notin` L → RhoCheck rho x (open_tm_wrt_tm a (a_Var_f x)))
    → Typing G (a_UAbs rho R a) (a_Pi rho A R B) R'.
Proof.
  intros.
  eapply E_Abs; eauto.
  pick fresh x.
  move: (H x ltac:(auto)) => h0.
  have h1: Ctx (x ~ Tm A R ++ G) by eauto.
  inversion h1. auto. Unshelve. auto.
Qed.

Lemma E_Conv2 : ∀ (G : context) (a B A : tm) R,
    Typing G a A R → DefEq G (dom G) A B a_Star R →
    Typing G a B R.
Proof.
  intros.
  eapply E_Conv; eauto.
  eapply DefEq_regularity in H0.
  inversion H0.
  auto.
Qed.

Lemma E_CPi2 :  ∀ (L : atoms) (G : context) (phi : constraint) (B : tm) R,
    (∀ c : atom, c `notin` L → Typing ([(c, Co phi)] ++ G) (open_tm_wrt_co B (g_Var_f c)) a_Star R) ->
    Typing G (a_CPi phi B) a_Star R.
Proof.
  intros.
  eapply E_CPi; eauto.
  pick fresh x.
  move: (H x ltac:(auto)) => h0.
  have h1: Ctx (x ~ Co phi ++ G); eauto.
  inversion h1. auto.
Qed.

Lemma E_CAbs2 : ∀ (L : atoms) (G : context) (a : tm) (phi : constraint) (B : tm) R,
       (∀ c : atom,
        c `notin` L → Typing ([(c, Co phi)] ++ G) (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co B (g_Var_f c)) R)
       → Typing G (a_UCAbs a) (a_CPi phi B) R.
Proof.
  intros.
  eapply E_CAbs; eauto.
  pick fresh x.
  move: (H x ltac:(auto)) => h0.
  have h1: Ctx (x ~ Co phi ++ G); eauto.
  inversion h1. auto. Unshelve. auto.
Qed.


Lemma E_AbsCong2
     : ∀ (L : atoms) (G : context) (D : available_props) (rho : relflag) (b1 b2 A1 B : tm) R R',
       (∀ x : atom,
        x `notin` L
        → DefEq ([(x, Tm A1 R)] ++ G) D (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x))
            (open_tm_wrt_tm B (a_Var_f x)) R')
       → (∀ x : atom, x `notin` L → RhoCheck rho x (open_tm_wrt_tm b1 (a_Var_f x)))
       → (∀ x : atom, x `notin` L → RhoCheck rho x (open_tm_wrt_tm b2 (a_Var_f x)))
       -> SubRole R R'
       → DefEq G D (a_UAbs rho R b1) (a_UAbs rho R b2) (a_Pi rho A1 R B) R'.
Proof.
  intros.
  eapply E_AbsCong; eauto.
  pick fresh x.
  move: (H x ltac:(auto)) => h0.
  have h1: Ctx (x ~ Tm A1 R ++ G) by eauto.
  inversion h1; auto.
Qed.

Lemma E_CAbsCong2
     : ∀ (L : atoms) (G : context) (D : available_props) (a b : tm) (phi1 : constraint) R
       (B : tm),
       (∀ c : atom,
        c `notin` L
        → DefEq ([(c, Co phi1)] ++ G) D (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co b (g_Var_f c))
                (open_tm_wrt_co B (g_Var_f c)) R) → DefEq G D (a_UCAbs a) (a_UCAbs b) (a_CPi phi1 B) R.
Proof.
  intros.
  eapply E_CAbsCong; eauto.
  pick fresh x.
  move: (H x ltac:(auto)) => h0.
  have h1: Ctx (x ~ Co phi1 ++ G) by eauto.
  inversion h1. auto.
Qed.

Lemma E_Fam2 : ∀ (G : context) (F : tyfam) (A a : tm) R,
       Ctx G
       → binds F (Ax a A R) toplevel → Typing G (a_Fam F) A R.
Proof.
  intros.
  eapply E_Fam; eauto.
  move: (toplevel_closed H0) => h0.
  eapply Typing_regularity. eauto.
Qed.


Lemma E_Wff2 : ∀ (G : context) (a b A : tm) R, Typing G a A R → Typing G b A R → PropWff G (Eq a b A R).
Proof.
  intros.
  eapply E_Wff; eauto.
  eapply Typing_regularity. eauto.
Qed.

(****************************)
(**** Regularity Tactics ****)
(****************************)

(*
Ltac reg H :=
  match type of H with
  (*
    | AnnTyping _ ?a ?A =>
      first
        [ let tpgA := fresh "tpg" A in move: (AnnTyping_regularity H) => tpgA
        | let tpgA := fresh "tpg"   in move: (AnnTyping_regularity H) => tpgA]
    | AnnDefEq _ _ ?g ?A ?B =>
      let KA := fresh "K" A in
      let KB := fresh "K" B in
      let g' := fresh "g" in
      let tpgA := fresh "tpg" A in
      let tpgB := fresh "tpg" B in
      (* let deqg' := fresh "deq" g' in *)
      move: (AnnDefEq_regularity H) => [KA [KB [g' [tpgA [tpgB (* deqg' *) _]]]]]
    (* FIXME: this is the same case than above, with less informative fresh names.
       This is needed because fresh can fail (like, seriously?)
       TODO: failproof version of fresh (will it be solved in ltac2?) *)
    | AnnDefEq _ _ ?g ?A ?B =>
      let KA   := fresh "K"   in
      let KB   := fresh "K"   in
      let g'   := fresh "g"   in
      let tpgA := fresh "tpg" in
      let tpgB := fresh "tpg" in
      (* let deqg' := fresh "deq" g' in *)
      move: (AnnDefEq_regularity H) => [KA [KB [g' [tpgA [tpgB (* deqg' *) _]]]]]
    | AnnIso _ _ ?g ?phi1 ?phi2 =>
      let pwfp1 := fresh "pwf" phi1 in
      let pwfp2 := fresh "pwf" phi2 in
      move: (AnnIso_regularity H) => [pwfp1 pwfp2]
      *)
    | _ ⊨ _ : a_Star / _ => fail 1
    | _ ⊨ _ : _ / _ =>
      move: (Typing_regularity H) => ?
    | DefEq _ _ _ _ _ _ => (* TODO: do we want to name arguments? (like above) *)
      move: (DefEq_regularity2 H) => [? ?]
    

  end. 

(* TODO: extend (for now, it assumes that we only need regularity on defeq hyps - there are other use cases in other files) *)
Ltac autoreg :=
  repeat match goal with
    | [ H: AnnDefEq _ _ _ _ _ |- _ ] =>
      reg H; wrap_hyp H
    | [ H: AnnIso _ _ _ _ _ |- _ ] =>
      reg H; wrap_hyp H
    | [ H: _ ⊨ _ : _ / _ |- _ ] =>
      reg H; wrap_hyp H
    | [ H: DefEq _ _ _ _ _ _ |- _ ] =>
      reg H; wrap_hyp H
  end;
  unwrap_all. *)


(****************************)
(**** Inversion Tactics ****)
(****************************)

Ltac autoinv :=
  repeat match goal with  
    | [H : _ ⊨ a_App _ Rel _ _   : _ / _ |- _] => eapply invert_a_App_Rel in H; pcess_hyps
    | [H : _ ⊨ a_App _ Irrel _ _ : _ / _ |- _] => eapply invert_a_App_Irrel in H; pcess_hyps
    | [H : _ ⊨ a_App _ ?ρ _ _    : _ / _ |- _] => destruct ρ
    | [H : _ ⊨ a_CApp _ _        : _ / _ |- _] => eapply invert_a_CApp in H; pcess_hyps
    | [H : _ ⊨ a_UAbs _ _ _      : _ / _ |- _] => eapply invert_a_UAbs in H; pcess_hyps
    | [H : _ ⊨ a_UCAbs _         : _ / _ |- _] => eapply invert_a_UCAbs in H; pcess_hyps
    | [H : _ ⊨ a_Conv _ _ _      : _ / _ |- _] => eapply invert_a_Conv2 in H; pcess_hyps
  (* TODO *)
  end.

