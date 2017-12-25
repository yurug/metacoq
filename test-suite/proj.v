Require Import Template.Template.
Require Import String.
Set Primitive Projections.

Record Eq (A : Type) := { eq : A -> A -> bool; eq_proof : forall x y, eq x y = true <-> x = y }.

Program Definition eqnat : Eq nat := {| eq x y := true |}.
Next Obligation. Admitted.

Quote Recursively Definition eqnatr := eqnat.

Goal forall {A} {e : Eq A} x y, e.(eq _) x y = eq _ e x y.
Proof.
  intros.
  match goal with
   |- ?T => quote_term T (fun x => pose (qgoal:=x))
  end.
Show.
  match goal with
    H:= context [Ast.tProj (Ast.mkInd "Top.proj.Eq" 0, 1, 0) _] |- _ => idtac
  end.
  reflexivity.
Qed.