From Coq Require Import Sets.Ensembles.
From Coq Require Import Sets.Powerset_facts.

(*Formulas: *)

Inductive Formula : Type :=
    | atom : nat -> Formula
    | disj : Formula -> Formula -> Formula
    | conj : Formula -> Formula -> Formula
    | imp : Formula -> Formula -> Formula
    | neg : Formula -> Formula
    | bot : Formula. 

Notation "~T" := (bot) (at level 0, left associativity).
Notation "#' f" := (atom f) (at level 1, left associativity).  
Notation "~' f" := (neg f) (at level 38, left associativity).
Notation "f1 /\' f2 " := (conj f1 f2) (at level 39, left associativity).
Notation "f1 \/' f2 " := (disj f1 f2) (at level 40, left associativity).
Notation "f1 ->' f2 " := (imp f1 f2) (at level 41, right associativity).


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
    | negI (C:Ensemble Formula) (f :Formula) (H: ND (Union Formula C (Singleton Formula f)) bot ): ND C (neg f) 
    | botE (C:Ensemble Formula) (f:Formula) (H:ND C bot):ND C f
    | RAA (C:Ensemble Formula) (f:Formula) (H:ND (Union Formula C (Singleton Formula (neg f))) bot):ND C f.

Notation "C |- f " := (ND C f) (at level 20, left associativity).



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

Notation "model |= f" := (val model f) (at level 20, left associativity).

(*a model satisfying a set of formulae*)
(*model|=Gamma*)
Definition mSsf (model : nat -> bool) (Gamma:Ensemble Formula)  : Prop:=
    forall (f:Formula), (In Formula Gamma f -> (val model f = true)).

Notation "model |=' Gamma" := (mSsf model Gamma) (at level 20, left associativity).

(*All models satisfying elements of Gamma are satisfying F*)
(*Gamma|=f*)
Definition sfSf (Gamma: Ensemble Formula) (f:Formula) : Prop:=
    forall (model: nat ->bool),( mSsf model Gamma -> val model f = true).

Notation "Gamma |='' f" := (sfSf Gamma f) (at level 20, left associativity).






(*Proof by Contradiction*)
Axiom pbc : forall (P: Prop), (~P -> False) -> P.
Axiom dnegE1 : forall P:Prop, (~~P->P).
Axiom dnegE2 : forall P:Prop, (P->~~P).
Axiom excluded_middle : forall P:Prop, P \/ ~P.

Lemma Union_In : forall (U:Type) (A B : Ensemble U) (x:U),
In U A x \/ In U B x -> In U (Union U A B) x.
intros U A B x H. destruct H.
+apply Union_introl. apply H.
+apply Union_intror. apply H.
Qed.

(*needed to prove the next lemma*)
Lemma about_Union: forall (A:Ensemble Formula)(f1 f2: Formula),
    Union Formula (Union Formula A (Singleton Formula f1)) (Singleton Formula  f2)=
    Union Formula (Union Formula A (Singleton Formula  f2)) (Singleton Formula f1).
    Proof. intros A f1 f2. rewrite ->Union_associative. 
    rewrite ->Union_commutative with (A:=(Singleton Formula f1)).
    rewrite ->Union_associative. reflexivity.  
Qed.

Lemma Weakening: forall(C:Ensemble Formula) (f1 f2:Formula), C |- f1 -> Union Formula C (Singleton Formula f2) |- f1.
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


Lemma Strong_Weakening: forall(C G:Ensemble Formula) (f :Formula), C |- f -> Union Formula C G |- f.
    intros C G f H. induction H.
    +apply ax. apply Union_introl. apply H.
    +apply conjE1 in IHND. apply IHND.
    +apply conjE2 in IHND. apply IHND.
    +apply conjI. -apply IHND1. -apply IHND2.
    Admitted.