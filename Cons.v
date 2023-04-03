From Coq Require Import Sets.Ensembles.
From Coq Require Import Sets.Powerset_facts.
Require Import Logic_and_Set_Theory.

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
Lemma Cons_Prop : forall Gamma : Ensemble Formula,
Gamma |- ~T -> forall f:Formula, Gamma |- f /\ Gamma |- (~' f).
Proof. 
    intros Gamma H f. split.
    +apply botE. apply H.
    +apply botE. apply H.
Qed.

Lemma Cons_Prop0: forall (Gamma Gamma' : Ensemble Formula),
Cons Gamma -> Included Formula Gamma' Gamma -> Cons Gamma'.
Proof.
    intros Gamma Gamma' H H0 H1. apply Strong_Weakening with (G:=Gamma) in H1.
    apply Union_absorbs in H0. rewrite -> Union_commutative in H0. rewrite -> H0 in H1.
    apply H. apply H1.
    Qed.





