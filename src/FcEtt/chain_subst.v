Require Import FcEtt.imports.
Require Import FcEtt.tactics.
Require Import FcEtt.notations.
Require Import FcEtt.utils.

Require Import FcEtt.ett_ott.

Require Import FcEtt.ett_inf.
Require Import FcEtt.ett_ind.
Require Import FcEtt.ext_wf.
Require Export FcEtt.ext_invert.
Require Export FcEtt.ext_weak.
Require Export FcEtt.ext_subst.
Require Import FcEtt.ett_roleing.

Require Import FcEtt.param.
Require Import FcEtt.ett_path.
Require Import FcEtt.ett_match.
Require Import FcEtt.ett_rename.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.




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

Definition pattern_arg_subst_co : pattern_arg -> atom -> co -> co :=
 fun arg x b =>
  match arg with 
  | p_Tm nu a => tm_subst_tm_co a x b
  | p_Co _    => co_subst_co_co g_Triv x b
  end.


(* This operation applies that substitution to an arbitrary tm *)
Definition cps_tm : tm -> list (atom * pattern_arg) -> tm :=
  fold_right (fun '(x,y) b => pattern_arg_subst_tm y x b).

Definition cps_co : co -> list (atom * pattern_arg) -> co :=
  fold_right (fun '(x,y) b => pattern_arg_subst_co y x b).


Definition cps_constraint phi sub :=
  match phi with 
  | Eq a b A R => Eq (cps_tm a sub) (cps_tm b sub) (cps_tm A sub) R
  end.
Definition cps_sort (s : sort) sub :=
  match s with 
  | Tm A   => Tm (cps_tm A sub)
  | Co phi => Co (cps_constraint phi sub)
  end.
Definition cps_context (G : context) su : context :=
  EnvImpl.map (fun so => cps_sort so su) G.

Definition cps_pattern_arg pa s :=
  match pa with 
  | p_Tm nu a => p_Tm nu (cps_tm a s)
  | p_Co g    => p_Co (cps_co g s)
  end.


(* Predicates about these substitutions *)

Definition lc_sub (sub:list(atom*pattern_arg)) :=
  Forall (fun '(x,p) => lc_pattern_arg p) sub.

(*
Definition rngFresh x (sub:list(atom*pattern_arg)) :=
  Forall (fun '(y,t) => x `notin` singleton y `union` (fv_tm_tm_pattern_arg t)) sub.
*)

(* cps properties --- homemorphic over term forms *)

Lemma cps_a_CPi : forall phi C sub, 
    cps_tm (a_CPi phi C) sub = 
        (a_CPi (cps_constraint phi sub) 
               (cps_tm C sub)).
Proof.
  intros. induction sub; destruct phi; simpl; auto.
  destruct a; simpl; rewrite IHsub.
  destruct p; simpl; auto.
Qed.

Lemma cps_a_Pi : forall nu A B sub,
   cps_tm (a_Pi nu A B) sub = 
               a_Pi nu (cps_tm A sub)
                        (cps_tm B sub).
Proof. 
  intros. induction sub; simpl; auto.
  destruct a; simpl. rewrite IHsub.
  destruct p; simpl; auto.
Qed.

Lemma cps_a_App : forall l nu a1 a2,
           cps_tm (a_App a1 nu a2) l =
           a_App (cps_tm a1 l) nu 
                 (cps_tm a2 l).
Proof. intros. induction l. simpl; auto. 
       destruct a; simpl. rewrite IHl.
       destruct p; simpl; auto.
Qed.

Lemma cps_a_CApp : forall l a g, 
    cps_tm (a_CApp a g) l =
    a_CApp (cps_tm a l) (cps_co g l).
Proof. intros. induction l. simpl; auto. destruct a0; simpl.
       destruct p; rewrite IHl; auto.
Qed.

Lemma cps_g_Triv : forall s, 
    cps_co g_Triv s = g_Triv.
Proof. induction s; try destruct p; simpl; auto.
destruct a. rewrite IHs. destruct p. simpl. auto. simpl. auto.
Qed.

Lemma cps_a_Bullet : forall s, 
    cps_tm a_Bullet s = a_Bullet.
Proof. induction s; try destruct p; simpl; auto.
destruct a. rewrite IHs. destruct p. simpl. auto. simpl. auto.
Qed.


Lemma cps_tm_apply_pattern_args : forall pargs hd s,  
   (cps_tm (apply_pattern_args hd pargs) s) =
      (apply_pattern_args 
         (cps_tm hd s) 
         (List.map (fun p => cps_pattern_arg p s) pargs)).
Proof. 
  induction pargs;
  intros; simpl; auto.
  destruct a; try destruct nu; try destruct rho; simpl;
  rewrite IHpargs; 
  try rewrite cps_a_App; 
  try rewrite cps_a_CApp; 
  try rewrite cps_a_Bullet;
  try rewrite cps_g_Triv;
  auto.
Qed.

(* ----------------------------------- *)

Lemma cps_tm_cons : forall nu a x s sub1, 
  tm_subst_tm_tm a x (cps_tm s sub1) =
  cps_tm s ((x, p_Tm nu a) :: sub1).
Proof.
  intros. simpl. auto.
Qed.

Lemma cps_co_cons : forall g x s sub1, 
  co_subst_co_tm g_Triv x (cps_tm s sub1) =
  cps_tm s ((x, p_Co g) :: sub1).
Proof.
  intros. simpl. auto.
Qed.


Lemma cps_nil : forall s,
  cps_tm s ∅ = s.
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

Lemma cps_sort_cons_co : forall x s sub1, 
  co_subst_co_sort g_Triv x (cps_sort s sub1) =
  cps_sort s ((x, p_Co g_Triv) :: sub1).
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

(* ----------------------------------- *)
(* Interaction with other functions *)


Lemma cps_open_tm_wrt_tm : forall C a sub,
    lc_sub sub ->
    cps_tm (open_tm_wrt_tm C a) sub
     = open_tm_wrt_tm (cps_tm C sub) 
                      (cps_tm a sub).
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

Lemma cps_open_tm_wrt_co : forall C a sub,
    lc_sub sub ->
    cps_tm (open_tm_wrt_co C a) sub
     = open_tm_wrt_co (cps_tm C sub) 
                      (cps_co a sub).
Proof.
  induction sub. simpl. auto.
  move=> LC. inversion LC.
  simpl. destruct a0. destruct p; simpl.
  inversion H1.
  rewrite IHsub; auto.
  rewrite tm_subst_tm_tm_open_tm_wrt_co; auto.
  inversion H1.
  rewrite IHsub; auto.
  rewrite co_subst_co_tm_open_tm_wrt_co. auto.
  auto.
Qed.


Lemma cps_close_tm_wrt_tm : forall C x sub,
    lc_sub sub ->
    x `notin` dom sub ->
    x `notin` fv_tm_tm_pattern_args_rng sub ->
    cps_tm (close_tm_wrt_tm x C) sub
     = close_tm_wrt_tm x (cps_tm C sub).
Proof.
  induction sub; intros; simpl; auto.
  destruct a. unfold fv_tm_tm_pattern_args_rng in *.
  destruct p; simpl in *; inversion H; subst; inversion H4; auto; subst.
  rewrite <- tm_subst_tm_tm_close_tm_wrt_tm; auto.
  rewrite IHsub; auto.
  rewrite <- co_subst_co_tm_close_tm_wrt_tm; auto.
  rewrite IHsub; auto.
Qed.

Lemma cps_tm_tm_subst_tm_tm: forall b a x sub, 
    lc_sub sub ->
    x `notin` dom sub ->
    x `notin` fv_tm_tm_pattern_args_rng sub ->
    tm_subst_tm_tm (cps_tm a sub) x (cps_tm b sub)
    = cps_tm (tm_subst_tm_tm a x b) sub.
Proof.
  intros.
  rewrite (tm_subst_tm_tm_spec b a x).
  rewrite cps_open_tm_wrt_tm; auto.
  rewrite cps_close_tm_wrt_tm; auto.
  rewrite tm_subst_tm_tm_spec.
  auto. 
Qed.

Lemma cps_tm_fresh_eq : forall a sub,
    domFresh sub (fv_tm_tm_tm a) ->
    domFresh sub (fv_co_co_tm a) ->
    cps_tm a sub = a.
Proof. 
  induction sub; intros; simpl; auto.
  inversion H; subst.
  inversion H0; subst.
  destruct a0; destruct p; simpl in *.
  rewrite tm_subst_tm_tm_fresh_eq; auto.
  rewrite IHsub; auto.
  rewrite co_subst_co_tm_fresh_eq; auto.
  rewrite IHsub; auto.
Qed. 

Lemma cps_co_fresh_eq : forall a sub,
    domFresh sub (fv_tm_tm_co a) ->
    domFresh sub (fv_co_co_co a) ->
    cps_co a sub = a.
Proof. 
  induction sub; intros; simpl; auto.
  inversion H; subst.
  inversion H0; subst.
  destruct a0; destruct p; simpl in *.
  rewrite tm_subst_tm_co_fresh_eq; auto.
  rewrite IHsub; auto.
  rewrite co_subst_co_co_fresh_eq; auto.
  rewrite IHsub; auto.
Qed. 



Lemma cps_subst_var : forall sub0 x nu a2,  
    lc_sub sub0 ->
    x ∉ dom sub0 ->
    x ∉ fv_tm_tm_pattern_args_rng sub0 ->
    domFresh sub0 (fv_tm_tm_tm a2) ->
    domFresh sub0 (fv_co_co_tm a2) ->
    cps_tm (a_Var_f x) ((x, p_Tm nu a2) :: sub0) = a2.
Proof.
  intros.
  simpl.
  replace a2 with (cps_tm a2 sub0). 2 :
    rewrite cps_tm_fresh_eq; auto.
  rewrite cps_tm_tm_subst_tm_tm; auto.
  rewrite tm_subst_tm_tm_var.
  auto.
Qed.

Inductive wf_sub (G : context) : list (atom * pattern_arg) -> Prop :=
  | wf_sub_nil     : wf_sub G nil
  | wf_sub_cons_tm : forall x nu a2 sub0, 
      wf_sub G sub0 ->
      lc_tm a2 ->
      x ∉ dom sub0 ->
      x ∉ dom G    ->
      (fv_tm_tm_tm a2) \u (fv_co_co_tm a2) [<=] dom G ->
      wf_sub G ((x,p_Tm nu a2)::sub0)
  | wf_sub_cons_co : forall x sub0, 
      wf_sub G sub0 -> 
      x ∉ dom sub0 ->
      x ∉ dom G    ->
      wf_sub G ((x,p_Co g_Triv)::sub0).

Hint Constructors wf_sub.

Lemma wf_sub_pattern_args :
  forall G sub, wf_sub G sub -> fv_tm_tm_pattern_args_rng sub [<=] dom G.
Proof. 
  induction 1; unfold fv_tm_tm_pattern_args_rng in *; simpl; eauto.
  fsetdec.
  rewrite IHwf_sub. fsetdec.
  rewrite IHwf_sub. fsetdec.
Qed. 

Lemma wf_sub_lc_sub : forall G sub, 
    wf_sub G sub -> lc_sub sub.
Proof. 
  induction 1; unfold lc_sub; eauto. 
Qed.

Hint Resolve wf_sub_lc_sub.

Lemma wf_sub_domFresh : forall G s sub, 
  s [<=] (dom G) -> wf_sub G sub -> domFresh sub s.
Proof. 
  intros. induction H0.
  all: unfold domFresh in *.
  all: eauto.
Qed.


Lemma wf_cps_subst_var : forall sub0 x G nu a2, 
    wf_sub G ((x, p_Tm nu a2) :: sub0) ->
    cps_tm (a_Var_f x) ((x, p_Tm nu a2) :: sub0) = a2.
Proof.
  intros.
  inversion H. subst.
  eapply cps_subst_var; eauto 1. eauto.
  move: (wf_sub_pattern_args H4) => h0.
  fsetdec.
  eapply wf_sub_domFresh; eauto.
  eapply wf_sub_domFresh; eauto.
Qed.

Lemma wf_cps_co_subst_var : forall sub0 x G g, 
    wf_sub G ((x, p_Co g) :: sub0) ->
    cps_co (g_Var_f x) ((x, p_Co g) :: sub0) = g_Triv.
Proof.
  intros.
  inversion H. subst.
  generalize dependent sub0.
  induction sub0; intros; simpl.
  destruct (x == x) eqn:h. rewrite h; auto. contradiction.
  destruct a.
  inversion H3; subst; simpl in *.
  + rewrite tm_subst_tm_co_fresh_eq; eauto.
    rewrite cps_co_fresh_eq; eauto.
    eapply wf_sub_domFresh; simpl; eauto. fsetdec.
    simpl. eapply domFresh_singleton2. fsetdec.
  + rewrite (co_subst_co_co_fresh_eq _ _ a); eauto.
    rewrite cps_co_fresh_eq; eauto; simpl.
    eapply domFresh_empty.
    eapply domFresh_singleton2. auto.
Qed.    

Lemma cps_pattern_fresh :  forall A pargs1 x p sub (G:list(atom*A)),
   x `notin` dom G ->
   fv_co_co_pattern_args (List.map (cps_pattern_arg^~ sub) pargs1) ⊂ empty ->
   fv_tm_tm_pattern_args (List.map (cps_pattern_arg^~ sub) pargs1) ⊂ dom G ->
   List.map (cps_pattern_arg^~ ((x, p) :: sub)) pargs1 = 
   List.map (cps_pattern_arg^~ sub) pargs1.
Proof. 
  intros A pargs0.
  induction pargs0; intros; simpl in *; auto.
  erewrite IHpargs0; eauto.
  destruct a; simpl in *; f_equal; f_equal.
  destruct p.
  simpl.
  rewrite tm_subst_tm_tm_fresh_eq; auto. 
  simpl.
  rewrite co_subst_co_tm_fresh_eq; auto. 
  fsetdec.
  destruct p.
  simpl.
  rewrite tm_subst_tm_co_fresh_eq; auto. 
  simpl.
  rewrite co_subst_co_co_fresh_eq; auto. 
  fsetdec.
Qed.
