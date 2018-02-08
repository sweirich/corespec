(* This file shows that we don't need irrelevant arguments in the presence of
   the phantom role.

   - After compiling irrelevant arguments to phm, the operational semantics is
     the same.

   - After compiling irrelevant arguments to phm, the terms will still type
     check (phantomize_mutual).

   - Do we need to show anything else?


*)



Require Import FcEtt.ett_ind.

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

Lemma phantomize_lc_tm : forall a, lc_tm a -> lc_tm (phantomize a).
Admitted.
Lemma phantomize_open :
  forall v b, (phantomize (open_tm_wrt_tm v b)) = 
         open_tm_wrt_tm (phantomize v) (phantomize b).
Admitted. 


(* -------------------------------------------------------- *)
(* Proofs that we actually care about.                      *)

Lemma phantomize_Beta :
  forall a b R, Beta a b R -> Beta (phantomize a) (phantomize b) R.
Proof.
  intros a b R H.
  destruct H; simpl.
  - destruct rho. rewrite phantomize_open.
    econstructor. eapply phantomize_lc_tm. auto. econstructor.
    admit.
    rewrite phantomize_open.
    econstructor. admit. admit.
  - admit.
  - admit.
  - econstructor.
Admitted.

Lemma phantomize_reduction_in_one :
  forall a b R, reduction_in_one a b R -> reduction_in_one (phantomize a) (phantomize b) R.
Proof.
Admitted.

Lemma phantomize_mutual :
  (forall G a A R, Typing G a A R ->
          Typing (phantomize_context G) (phantomize a) (phantomize A) R) /\
  (forall G phi, PropWff G phi ->
          PropWff (phantomize_context G) (phantomize_constraint phi)) /\
  (forall G D p1 p2, Iso G D p1 p2 ->
          Iso (phantomize_context G) D
              (phantomize_constraint p1) (phantomize_constraint p2)) /\
  (forall G D g a b R,
      DefEq G D g a b R  ->
      forall A, Typing G a A R ->
             DefEq (phantomize_context G) D (phantomize a) (phantomize b) (phantomize A) R) /\
  (forall G, Ctx G -> Ctx (phantomize_context G) /\
    forall c t, binds c t G -> binds c (phantomize_sort t) (phantomize_context G)).
Admitted.

