From Coq Require Import Sets.Ensembles.
From Coq Require Import Sets.Powerset_facts.
From CPL Require Import Logic_and_Set_Theory.
From CPL Require Import Cons.
(*These should transfer to Logic_and_Set_Theory.v:*)

(*This may be useful to do a prove by contradiction:*)
(*~ (~ (~ Q)) -> (~ Q)*)
(*++++++++++++++++++++++++++++++++++*)





(*----------------------------------*)
(*These should transfer to Cons.V:*)


(*----------------------------------*)
Definition maxCons (Gamma : Ensemble Formula) : Prop :=
    Cons Gamma -> forall Gamma' : Ensemble Formula, Included Formula Gamma' Gamma.


Lemma ex_of_max : forall (Gamma : Ensemble Formula),
Cons Gamma ->
exists Gamma' : Ensemble Formula,
 Included Formula Gamma Gamma' /\ Cons Gamma'.
 Proof. intros Gamma H.