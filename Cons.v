From Coq Require Import Sets.Ensembles.
From Coq Require Import Sets.Powerset_facts.
Require Import Logic_and_Set_Theory.




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

(*The following axiom seems necessary for what we want to do! Better to transfer it to Cons.v*)
(*It seems possible to prove it, while defining Gamma as a finite ensemble, which may be sufficient to satisfy our needs!*)
Axiom lem_for_consistency: forall Gamma: Ensemble Formula,
Cons Gamma \/ ~Cons Gamma.




