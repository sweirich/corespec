(* Tools for dependent programming *)

Require FcEtt.imports.


Notation "f >-> g" := (fun x => (g (f x))) (at level 70).

Inductive sig2el (A:Type) (B:Type) (P : A -> B -> Prop) : Type :=
    exist2el : forall (x : A) (y : B), P x y -> sig2el P.

Notation "{ x , y | P }" := (sig2el (fun x y => P)) (at level 0, x at level 99, y at level 99) : type_scope.


Notation "'yeah'"      := (left _ _).
Notation "'nope'"      := (right _ _).

Notation "<< x >>"     := (inleft _ (exist _ x _)).
Notation "<< x , y >>" := (inleft _ (exist2el _ x y _)).
Notation "!!"          := (inright _ _).


Hint Resolve inleft inright left right.