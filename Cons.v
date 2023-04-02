From Coq Require Import Sets.Ensembles.
From Coq Require Import Sets.Powerset_facts.
From CPL Require Import Logic_and_Set_Theory.

(*These should transfer to Logic_and_Set_Theory.v:*)
(*A useful lemma for working with the definition of consistency.*)
Lemma prop_double_neg_I : forall P:Prop, P -> ~~P.
intros P H H1. apply H1 in H. apply H.
Qed. 
(*----------------------------------*)




(*Consistency:*)
Definition Cons (Gamma : Ensemble Formula) : Prop :=
~(Gamma |- ~T).

(*Required Lemmas:*)






