From Coq Require Import Sets.Ensembles.
From Coq Require Import Powerset_facts.
(*Formulas: *)

Inductive Formula : Type :=
    | atom : nat -> Formula
    | disj : Formula -> Formula -> Formula
    | conj : Formula -> Formula -> Formula
    | imp : Formula -> Formula -> Formula
    | neg : Formula -> Formula
    | bot : Formula. 

(*Natural Deduction: *)

Inductive ND : Ensemble Formula -> Formula -> Prop :=
    | ax (C:Ensemble Formula) (f: Formula) (H:In Formula C  f) : ND C f
    | conjE1 (C:Ensemble Formula) (f1 f2: Formula) (H:ND C (conj f1 f2)) : ND C f1
    | conjE2 (C:Ensemble Formula) (f1 f2: Formula) (H:ND C (conj f1 f2)) : ND C f2
    | conjI (C:Ensemble Formula) (f1 f2: Formula) (H1:ND C f1) (H2:ND C f2) : ND C (conj f1 f2)
    | disjE (C:Ensemble Formula) (f1 f2 f:Formula) (H1:ND (Union Formula C (Singleton Formula f1)) f) 
        (H2:ND (Union Formula C (Singleton Formula f2)) f) (H3:ND C (disj f1 f2) ): ND C f 
    | disjI1 (C:Ensemble Formula) (f1 f2:Formula) (H:ND C f1):ND C (disj f1 f2)
    | disjI2 (C:Ensemble Formula) (f1 f2:Formula) (H:ND C f2):ND C (disj f1 f2)
    | impE (C:Ensemble Formula) (f1 f2:Formula) (H1:ND C (imp f1 f2)) (H2:ND C (f1)): ND C f2
    | impI (C:Ensemble Formula) (f1 f2:Formula) (H:ND (Union Formula C (Singleton Formula f1)) f2): ND C (imp f1 f2)
    | negE (C:Ensemble Formula) (f :Formula) (H1: ND C f) (H2: ND C (neg f)): ND C bot
    | negI (C:Ensemble Formula) (f :Formula) (H: ND (Union Formula C (Singleton Formula f)) bot ): ND C (neg f) (*Momkene context ghalat bashe!!!*)
    | botE (C:Ensemble Formula) (f:Formula) (H:ND C bot):ND C f
    | RAA (C:Ensemble Formula) (f:Formula) (H:ND (Union Formula C (Singleton Formula (neg f))) bot):ND C f.

(*Hilbert: *)

Inductive Hilb : Ensemble Formula -> Formula -> Prop :=
    | Hax (C:Ensemble Formula) (f: Formula) (H:In Formula C  f) : Hilb C f
    | A1 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp f1 (imp f2 f1))
    | A2 (C:Ensemble Formula) (f1 f2 f3: Formula)  : Hilb C (imp (imp f1 (imp f2 f3)) (imp (imp f1 f2) (imp f1 f3)))
    | A3 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp (conj f1 f2) f1)
    | A4 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp (conj f1 f2) f2)
    | A5 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp f1 (imp f2 (conj f1 f2)))
    | A6 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp f1 (disj f1 f2) )
    | A7 (C:Ensemble Formula) (f1 f2: Formula)  : Hilb C (imp f2 (disj f1 f2) )
    | A8 (C:Ensemble Formula) (f1 f2 f3: Formula)  : Hilb C (imp (imp f1 f3) (imp (imp f2 f3) (imp (disj f1 f2) f3)) )
    | A9 (C:Ensemble Formula) (f1: Formula)  : Hilb C (imp bot f1 )
    | A10 (C:Ensemble Formula) (f1: Formula)  : Hilb C (disj f1 (neg f1))
    | MP (C:Ensemble Formula) (f1 f2:Formula) (H1:Hilb C (imp f1 f2)) (H2:Hilb C (f1)): Hilb C f2.

(*Semantics: *)

Fixpoint val  (model : nat -> bool) (f: Formula) : bool:=
    match f with
    | atom n=> model n
    | neg f1 =>  negb(val model f1)
    | disj f1 f2 => orb (val model f1) (val model f2)
    | conj f1 f2 =>andb (val model f1 ) (val model f2)
    | imp f1 f2 => orb(negb(val model f1))  (val model f2)
    | bot => false
    end.

(*a model satisfying a set of formulae*)
(*model|=Gamma*)
Definition mSsf (model : nat -> bool) (Gamma:Ensemble Formula)  : Prop:=
    forall (f:Formula), (In Formula Gamma f -> (val model f = true)).


(*All models satisfying elements of Gamma are satisfying F*)
(*Gamma|=f*)
Definition sfSf (Gamma: Ensemble Formula) (f:Formula) : Prop:=
    forall (model: nat ->bool),( mSsf model Gamma -> val model f = true).








(*Proof by Contradiction*)
Axiom pbc : forall (P: Prop), (~P -> False) -> P.






(*Consistency:*)
(*Inductive Cons1 : Ensemble Formula -> Prop :=
|cons1 (Gamma: Ensemble Formula) (H:~(ND Gamma bot)): Cons1 Gamma.*)
Definition Cons (Gamma : Ensemble Formula) : Prop :=
~(ND Gamma bot).

Definition iCons (Gamma : Ensemble Formula) : Prop :=
(ND Gamma bot).




(*needed to prove the next lemma*)
Lemma about_Union: forall (A:Ensemble Formula)(f1 f2: Formula),
    Union Formula (Union Formula A (Singleton Formula f1)) (Singleton Formula  f2)=
    Union Formula (Union Formula A (Singleton Formula  f2)) (Singleton Formula f1).
    Proof. intros A f1 f2. rewrite ->Union_associative. 
    rewrite ->Union_commutative with (A:=(Singleton Formula f1)).
    rewrite ->Union_associative. reflexivity.  
Qed.

Lemma Weakening: forall(C:Ensemble Formula) (f1 f2:Formula), ND C f1 -> ND (Union Formula C (Singleton Formula f2)) f1.
Proof.
    intros C f1 f2 H. induction H.
    +apply ax. apply Union_introl. apply H.
    +apply conjE1 in IHND. apply IHND.
    +apply conjE2 in IHND. apply IHND.
    +apply conjI. -apply IHND1. -apply IHND2.
    +apply disjE with (C:=Union Formula C (Singleton Formula f2)) (f1:=f1) (f2:=f0).
        -rewrite ->about_Union. apply IHND1.
        -rewrite ->about_Union. apply IHND2.
        -apply IHND3.
    +apply disjI1. apply IHND.
    +apply disjI2. apply IHND.
    +apply impE with (f1:=f1) (f2:=f0).
        -apply IHND1. -apply IHND2.
    +apply impI. rewrite ->about_Union. apply IHND.
    +apply negE with(f:=f). -apply IHND1. -apply IHND2.
    +apply negI. rewrite ->about_Union. apply IHND.
    +apply botE. apply IHND.
    +apply RAA. rewrite ->about_Union. apply IHND.
    Qed. 


(*Lemma 1.4.5 (used in main proof!) *)
Lemma ConsSyns0: forall (Gamma:Ensemble Formula) (f:Formula),
iCons(Union Formula Gamma (Singleton Formula (neg f))) <-> ND Gamma f.
Proof.
    intros Gamma f.
    split.
    +intros H. unfold iCons in H. apply RAA in H. apply H.
    +intros H. unfold iCons. apply negE with (f:=f). -apply Weakening. apply H. 
        -apply ax. apply Union_intror. apply In_singleton.
    Qed.

Axiom contraposition : forall (P Q :Prop), (P <-> Q) -> (~P <-> ~Q).
Lemma ConsSyns: forall (Gamma:Ensemble Formula) (f:Formula),
~iCons(Union Formula Gamma (Singleton Formula (neg f))) <-> ~ND Gamma f.
Proof.
  intros Gamma f.
  apply contraposition. apply ConsSyns0.
  Qed.




(*/neat*)
(*Existence of Model:*)  
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

Definition chain (U:Type) (R: relation U) (S : Ensemble U)  : Prop :=
    forall x y:U, In U S x -> In U S y -> (R x y \/ R y x).

Definition maximal (U:Type) (x:U) (R:relation U) : Prop:=
    forall y:U, R x y -> x=y.

Definition chain_sup (U:Type) (R: relation U) (S:Ensemble U) (sup:U): Prop:=
    chain U R S -> forall x:U, In U S x -> R x sup.


Axiom Zorn's_Lemma: forall (U:Type) (R:relation U), 
    pao U R /\ (forall (S: Ensemble U), (chain U R S -> exists (sup:U), chain_sup U R S sup) )
    -> exists (maxim:U), maximal U maxim R.


(*Lemma 1.4.10:*)

Definition Inc : relation (Ensemble Formula) := Included Formula.

Lemma Ex_of_Max0: forall (Gamma : Ensemble Formula), 
    Cons Gamma -> (exists (Gammap : Ensemble Formula),
        (maximal (Ensemble Formula) Gammap Inc ) /\ Inc Gamma Gammap).
Proof.
    intros Gamma H. exists Gamma. split.    
(*Here!
You Probably need to change statement of the Lemma, maybe you should break it
into several Lemmas in order to make it possible to prove.*)








(*Previous attemp for Lemma 1.4.10!:*)
Definition maxCons (Gamma : Ensemble Formula) : Prop:=
    Cons Gamma /\ forall (Gammap : Ensemble Formula), Included Formula Gamma Gammap
        /\ Cons Gammap -> Included Formula Gammap Gamma.

Definition TheSet (Gamma : Ensemble Formula) (X:Ensemble Formula) : Prop :=
    Cons X /\ Included Formula Gamma X.

Lemma Ex_of_Max : forall (Gamma:Ensemble Formula),
    Cons Gamma -> exists (Gammap:Ensemble Formula), 
    Included Formula Gamma Gammap /\ maxCons Gammap.
 Admitted.

(*Function in Lemma 1.4.11:*)

Axiom TheV : nat->bool.
Axiom VProp : forall (n : nat), TheV n=true <-> In Formula Gamma (atom n)  


Definition The (x : nat) : Prop := False.

(*The Lemma:*)
Lemma Existence_of_Model: forall (Gamma : Ensemble Formula),
~iCons Gamma -> exists (model : nat -> bool), mSsf model Gamma. 
Proof. Admitted.



(*neat/*)
(*My own Lemma!*)
Lemma UnionR : forall (Gamma:Ensemble Formula) (f:Formula) (model: nat -> bool),
mSsf model (Union Formula Gamma (Singleton Formula(neg f))) ->(mSsf model Gamma  /\ val model f = false).
Proof.
    intros Gamma f model H.
    split.
    +unfold mSsf. unfold mSsf in H.
        intros f0 H1. apply H. apply Union_introl.  
        apply H1.
    +unfold mSsf in H. 
        assert (H1: val model (neg f) = true -> val model f = false).
        {intros H2. simpl in H2. assert (H3:forall (b:bool), negb b=true -> b= false).
        {intros b. intros H4. induction b. +simpl in H4. rewrite -> H4. reflexivity.
        +reflexivity.  }
        apply H3 in H2.
        apply H2. }
        apply H1. apply H. apply Union_intror. apply In_singleton. 
        
Qed.




(*The Theorem!!!*)
Theorem Completeness: forall (Gamma:Ensemble Formula) (f:Formula) , 
sfSf Gamma f -> ND Gamma f.
Proof.
intros Gamma f. intros H.
apply pbc. intros H1. apply ConsSyns in H1. 
apply Existence_of_Model in H1.
inversion H1.
apply UnionR in H0. 
unfold sfSf in H. destruct H0. apply H in H0.
rewrite -> H2 in H0. discriminate.
Qed.


    



