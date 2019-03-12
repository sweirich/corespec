Require Export Coq.Unicode.Utf8.

Require Export Coq.Program.Basics.
Require Export Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export FcEtt.ett_ott.

(* SSReflect *)


From Coq Require Export ssreflect ssrfun ssrbool.
Close Scope boolean_if_scope.
Global Open Scope general_if_scope.



(**** Global imports and settings ****)



Global Set Implicit Arguments.
Global Set Bullet Behavior "Strict Subproofs".

(* Masking this nasty notation from the stdlib *)
Notation sort := sort (only parsing).


(* Generalizable variables, so that we can use the implicit quantification `( )  *)
Global Generalizable Variables Γ D R ζ a b t A B T x y ρ.
(* Fix: coq doesn't recognize small indices (₀, ₁, etc) as actual indices *)
Global Generalizable Variables Γ₀ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅.
Global Generalizable Variables D₀ D₁ D₂ D₃ D₄ D₅.
Global Generalizable Variables R₀ R₁ R₂ R₃ R₄ R₅.
Global Generalizable Variables ζ₀ ζ₁ ζ₂ ζ₃ ζ₄ ζ₅.
Global Generalizable Variables a₀ a₁ a₂ a₃ a₄ a₅.
Global Generalizable Variables b₀ b₁ b₂ b₃ b₄ b₅.
Global Generalizable Variables t₀ t₁ t₂ t₃ t₄ t₅.
Global Generalizable Variables A₀ A₁ A₂ A₃ A₄ A₅.
Global Generalizable Variables B₀ B₁ B₂ B₃ B₄ B₅.
Global Generalizable Variables T₀ T₁ T₂ T₃ T₄ T₅.
Global Generalizable Variables x₀ x₁ x₂ x₃ x₄ x₅.
Global Generalizable Variables ρ₀ ρ₁ ρ₂ ρ₃ ρ₄ ρ₅.
