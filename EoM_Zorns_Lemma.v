Require Import Logic_and_Set_Theory.
From Coq Require Import Sets.Ensembles.
From Coq Require Import Sets.Powerset_facts.


(*Zorn's Lemma:*)
Definition relation (U:Type) := U -> U -> Prop.
Definition reflexive (U:Type) (R : relation U) : Prop :=
    forall x:U, R x x.
Definition transitive (U:Type) (R : relation U) : Prop :=
    forall x y z:U, R x y->R y z -> R x z.
Definition symmetric (U:Type) (R : relation U) : Prop :=
    forall x y:U, R x y-> R y x.
Definition antisymmetric (U:Type) (R : relation U) : Prop :=
    forall x y:U, R x y-> R y x-> x=y.
Definition pao (U:Type) (R: relation U ) : Prop :=
    reflexive U R /\ transitive U R /\ antisymmetric U R.

Definition chain (U:Type) (R: relation U) (S : Ensemble U) (T : Ensemble U)  : Prop :=
  pao U R /\ Included (U) T S /\(forall x y:U, In U T x -> In U T y -> (R x y \/ R y x)).

Definition maximal (U:Type) (S:Ensemble U) (x:U) (R:relation U) : Prop:=
    (forall y:U, In U S y -> R x y -> x=y) /\ In U S x.

Definition upper_bound (U:Type) (S:Ensemble U) (R: relation U) (T:Ensemble U) (ub:U): Prop:=
    (forall x:U, In U T x -> R x ub) /\ In U S ub.

Axiom Zorn's_Lemma: forall (U:Type) (S:Ensemble U) (R:relation U), 
    pao U R -> (forall (T: Ensemble U), (chain U R S T -> exists (s:U), upper_bound U S R T s) )
    -> exists (maxim:U), maximal U S maxim R .

    