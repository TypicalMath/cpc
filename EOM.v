From Coq Require Import Sets.Ensembles.
From Coq Require Import Sets.Powerset_facts.
Require Import Logic_and_Set_Theory.
Require Import Cons.
Require Import PropListing.
(*These should transfer to Logic_and_Set_Theory.v:*)

(*This may be useful to do a prove by contradiction:*)
(*~ (~ (~ Q)) -> (~ Q)*)
(*++++++++++++++++++++++++++++++++++*)





(*----------------------------------*)
(*These should transfer to Cons.V:*)


(*----------------------------------*)
Definition maxCons (Gamma : Ensemble Formula) : Prop :=
    Cons Gamma -> forall Gamma' : Ensemble Formula, Included Formula Gamma' Gamma.

(*Trying to show that the defined Gamma_maximal is actually the maximal consistent set for Gamma*)
Lemma def_max_is_max: forall (Gamma Gamma_maximal: Ensemble Formula),
Cons Gamma -> Gamma_maximal_Prop Gamma Gamma_maximal -> Included Formula Gamma Gamma_maximal /\ Cons Gamma_maximal.
Proof. intros Gamma Gamma_maximal H H1.
unfold Gamma_maximal_Prop in H1.
split.
+apply H1.
+destruct H1.

(*The Lemma in general form*)
Lemma ex_of_max : forall (Gamma : Ensemble Formula),
Cons Gamma ->
exists Gamma' : Ensemble Formula,
 Included Formula Gamma Gamma' /\ Cons Gamma'.
 Proof. intros Gamma H. exists 