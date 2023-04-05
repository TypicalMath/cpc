From Coq Require Import Lists.List.
From Coq Require Import Sets.Ensembles.
From Coq Require Import Sets.Powerset_facts.
Require Import Logic_and_Set_Theory.
Require Import Cons.


Section listing.



Variable F : nat -> Formula.
Lemma F_Prop_one_one : forall (n1 n2 : nat), F n1 = F n2 -> n1=n2.
Proof. Admitted.
Lemma F_Prop_surjective : forall f : Formula, exists n:nat, F n = f.
Proof. Admitted.
    (*We need F to be an onto function between naturals and formulas*)
(*Maybe we can build it! later...
By defining an onto map between all naturals and formulas.*)





Inductive Gamma_seq : Ensemble Formula -> Ensemble Formula -> Prop :=
| zero (Gamma Gamma_n : Ensemble Formula) : Gamma_seq Gamma Gamma 
| consis (n:nat) (Gamma Gamma_n : Ensemble Formula) (H0 : Gamma_seq Gamma Gamma_n) (H : Cons (Union Formula Gamma_n (Singleton Formula (F n)))):
Gamma_seq Gamma (Union Formula Gamma_n (Singleton Formula (F n)))
| iconsis (n:nat) (Gamma Gamma_n : Ensemble Formula) (H0 : Gamma_seq Gamma Gamma_n) (H : ~Cons (Union Formula Gamma_n (Singleton Formula (F n)))):
Gamma_seq Gamma Gamma_n.

Lemma Gamma_is_in_all_Gamma_n : forall (Gamma Gamma_n:Ensemble Formula), 
Gamma_seq Gamma Gamma_n -> Included Formula Gamma Gamma_n.
Proof.
    intros Gamma Gamma_n H. induction H.
    -unfold Included. intros. apply H.
    -unfold Included in IHGamma_seq. unfold Included. intros. apply Union_introl. apply IHGamma_seq. apply H1.
    -apply IHGamma_seq.
    Qed.

(*(a)*)
Lemma Gamma_seq_Cons :forall (Gamma Gamma_n : Ensemble Formula),
Cons Gamma -> Gamma_seq Gamma Gamma_n -> Cons Gamma_n.
Proof.
    intros Gamma Gamma_n H H0. induction H0.
    +apply H.
    +apply H1.
    +apply IHGamma_seq. apply H.
Qed.

(*These two axioms seem necessary for what we want to do! Better to transfer them to Cons.v*)
(*The second one can be proved for finite ensembles and the second one seems Unnecessary!*)
Axiom lem_for_consistency: forall Gamma: Ensemble Formula,
Cons Gamma \/ ~Cons Gamma.
Axiom dne_for_consistency :forall Gamma: Ensemble Formula,
~Cons Gamma -> Gamma |- ~T. 


(*This is the Definition of Gamma_star in the book! there is no need for Gamma to be consistent in this definition.
Definition of Gamma_n and Gamma_star is independent of consistency of Gamma*)
Definition Gamma_star_Def  (Gamma Gamma_star: Ensemble Formula):Prop:=
    (forall (Gamma_n:Ensemble Formula),
    Gamma_seq Gamma Gamma_n -> Included Formula Gamma_n Gamma_star) 
    /\ 
    (forall f:Formula,In Formula Gamma_star f -> exists (Gamma_n':Ensemble Formula),Gamma_seq Gamma Gamma_n' /\ In Formula Gamma_n' f).


Lemma Gamma_n_inclusion: forall (Gamma Gamma_n Gamma_n' :Ensemble Formula),
Gamma_seq Gamma Gamma_n -> Gamma_seq Gamma Gamma_n' -> 
Included Formula Gamma_n Gamma_n' \/ Included Formula Gamma_n' Gamma_n.
Proof.
    intros Gamma Gamma_n Gamma_n' H H1. induction H.
    -induction H1.
    --right. unfold Included. intros. apply H.
    --destruct IHGamma_seq.
    ---left. unfold Included. intros. apply Union_introl. apply H0. apply H2.
    ---left. apply Gamma_is_in_all_Gamma_n. apply consis with (n:=n) in H1. ----apply H1. ---- apply H.
    --destruct IHGamma_seq.
    ---left. apply H0.
    ---right. apply H0.
    -induction H1.
    --



(*for (b) *)
Lemma Gamma_star_Prop: forall (Gamma Gamma_star:Ensemble Formula) (f:Formula),
Gamma_star_Def Gamma Gamma_star-> Gamma_star |- f ->
exists (Gamma_n:Ensemble Formula), Gamma_seq Gamma Gamma_n /\
Gamma_n |- f.
Proof.
intros Gamma Gamma_star f H H0.
induction H0. rename C into Gamma_star. 

+unfold Gamma_star_Def in H. apply H in H0. destruct H0. destruct H0. exists x.
split. -apply H0. -apply ax. apply H1.

+apply IHND in H. destruct H as [Gamma_n]. exists Gamma_n.
split. -apply H. -destruct H. apply conjE1 in H1. apply H1.

+apply IHND in H. destruct H as [Gamma_n]. exists Gamma_n.
split. -apply H. -destruct H. apply conjE2 in H1. apply H1.

+assert (H1: Gamma_star_Def Gamma C). -apply H. -apply IHND1 in H. apply IHND2 in H1.
destruct H as [Gamma_n]. destruct H1 as [Gamma_n']. pose proof Gamma_n_inclusion as H3.
destruct H3 with (Gamma:=Gamma) (Gamma_n:=Gamma_n) (Gamma_n':=Gamma_n').
--apply H. --apply H0. 
--exists Gamma_n'. split. ---apply H0. ---apply conjI.
----destruct H. apply Strong_Weakening with (G:=Gamma_n') in H2. assert (H4:Union Formula Gamma_n Gamma_n' = Gamma_n').
-----rewrite <- Union_commutative. apply Union_absorbs. apply H1.
-----rewrite <- H4. apply H2.
----apply H0.
--exists Gamma_n. split. ---apply H. ---apply conjI.
----apply H. ----destruct H0. apply Strong_Weakening with (G:=Gamma_n) in H2. assert (H4:Union Formula Gamma_n' Gamma_n = Gamma_n).
-----rewrite <- Union_commutative. apply Union_absorbs. apply H1.
-----rewrite <- H4. apply H2.

+admit.
+apply IHND in H. destruct H as [n]. destruct H as [Gamma_n]. exists n. exists Gamma_n. destruct H.
split. -apply H. -apply disjI1. apply H1.
+apply IHND in H. destruct H as [n]. destruct H as [Gamma_n]. exists n. exists Gamma_n. destruct H.
split. -apply H. -apply disjI2. apply H1.
+assert (H1:Gamma_star_Def Gamma C). -apply H. -apply IHND1 in H. apply IHND2 in H1.
destruct H as [n]. destruct H as [Gamma_n]. destruct H1 as [n']. destruct H0 as [Gamma_n'].
 admit.
+admit.
+admit.


(*(b)*)
Lemma Gamma_star_Cons: forall (Gamma Gamma_star:Ensemble Formula),
    Cons Gamma -> Gamma_star_Def Gamma Gamma_star -> Cons Gamma_star.
Proof.
    intros Gamma Gamma_star H H0 H1. apply Gamma_star_Prop with (Gamma:=Gamma) in H1.
    +destruct H1 as [Gamma_n]. destruct H1. apply prop_double_neg_I in H2. 
    pose proof Gamma_seq_Cons as H3. assert(H4: ~ Cons Gamma_n).
    ++apply H2.
    ++apply H4. apply H3 with (Gamma:=Gamma).
    +++apply H.
    +++apply H1.
    +apply H0.
    Qed. 
    
















(*It was supposed to be the definition for instead of the next one!
Fixpoint Gamma_seq_Prop (Gamma Gamma_n: Ensemble Formula) (n:nat) : Prop :=
    (n = 0 -> Gamma_seq_Prop Gamma Gamma 0) (*Gamma = Gamma_n???Isn't it better?!*)
    /\ (n <>0 -> ((Union Formula Gamma_n (Singleton Formula (F n))) |- ~T) -> (Gamma_seq_Prop Gamma Gamma_n (n+1)))
    /\ n <>0 -> Cons (Union Formula Gamma_n (Singleton Formula (F n))) -> Gamma_seq_Prop Gamma (Union Formula Gamma_n (Singleton Formula (F n))) (n+1).*)
(*This Prop, defines Gamma_star from Gamma by determining which formulas it includes and which formulas it doesn't!*)
Definition Gamma_star_Prop (Gamma : Ensemble Formula) (n:nat) (Gamma_star : Ensemble Formula) : Prop :=
    (Included Formula Gamma Gamma_star)
    /\ ((Union Formula Gamma_star (Singleton Formula (F n))) |- ~T <-> ~ In Formula Gamma_star (F n))    
    /\ (Cons (Union Formula Gamma_star (Singleton Formula (F n))) <-> In Formula Gamma_star (F n)). 

Lemma Gamma_star_Cons : forall (Gamma Gamma_star : Ensemble Formula),
Cons Gamma ->forall n : nat , Gamma_star_Prop Gamma n Gamma_star ->
Cons Gamma_star.
Proof.
    intros Gamma Gamma_star H n H0. unfold Gamma_star_Prop in H0.
    destruct H0. destruct H1.
    
    induction n. 
    +unfold Cons. intros H3. admit.
    + 





    Inductive Gamma_seq_Prop (Gamma : Ensemble Formula) (f:seq Formula) (n : nat) (Gamma_n : Ensemble Formula) : Prop:=
    | zero (H: n=0) : Gamma_seq_Prop Gamma f 0 Gamma
    | consi (H: )
(*Proposition about the above function which completes its definition:*)
Definition seq_Cons_Prop (Gamma : Ensemble Formula) (f:seq Formula) (n : nat) : Prop:=
Cons (Gamma_seq Gamma f n) ->  Cons (Gamma_seq Gamma f (S n)).


(*The lemma about our defined function*)
Lemma seq_Cons :
    forall (Gamma : Ensemble Formula) (f:seq Formula) (n: nat),
    Cons Gamma -> seq_Cons_Prop Gamma f n -> Cons (Gamma_seq Gamma f n).
    Proof.
        intros Gamma f n H H1. induction n.
        +apply H.
        +simpl. unfold seq_Cons_Prop in H1. 

(*Proposition Defining the Gamma* in book:*)
Definition Gamma_maximal_Prop (Gamma : Ensemble Formula) (Gamma_maximal : Ensemble Formula): Prop:=
    Included Formula Gamma Gamma_maximal  /\ 
    (forall (n:nat) (f:seq Formula),Included Formula (Gamma_seq Gamma f n) Gamma_maximal) /\
    (forall (phi : Formula) (f: seq Formula), In Formula Gamma_maximal phi -> exists n : nat, In Formula (Gamma_seq Gamma f n) phi). 



Lemma Gamma_maximal_consistency: 
forall (Gamma Gamma_maximal : Ensemble Formula ),
Cons Gamma -> Gamma_maximal_Prop Gamma Gamma_maximal -> Cons Gamma_maximal.
intros Gamma Gamma_maximal H H0. unfold Gamma_maximal_Prop in H0.
destruct H0. destruct H1. induction H1.

unfold Cons. intros H2.
assert (phi:Formula). +apply (atom 0). +apply Cons_Prop with (f:=phi) in H2.
destruct H2.
