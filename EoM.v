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





Inductive Gamma_seq : nat -> Ensemble Formula -> Ensemble Formula -> Prop :=
| zero (Gamma Gamma_n : Ensemble Formula) : Gamma_seq 0 Gamma Gamma 
| consis (n:nat) (Gamma Gamma_n : Ensemble Formula) (H0 : Gamma_seq n Gamma Gamma_n) (H : Cons (Union Formula Gamma_n (Singleton Formula (F n)))):
Gamma_seq (S n) Gamma (Union Formula Gamma_n (Singleton Formula (F n)))
| iconsis (n:nat) (Gamma Gamma_n : Ensemble Formula) (H0 : Gamma_seq n Gamma Gamma_n) (H : ~Cons (Union Formula Gamma_n (Singleton Formula (F n)))):
Gamma_seq (S n) Gamma Gamma_n.

(*The next two lemmas were defined to use for the lemma Gamma_n_equality. But may be useful anyway!*)
Lemma Gamma_equality : forall (Gamma Gamma' : Ensemble Formula),
Gamma_seq 0 Gamma Gamma' -> Gamma = Gamma'.
Proof.
    intros. inversion H. reflexivity.
    Qed.

Lemma Gamma_inclusion_0: forall (Gamma Gamma':Ensemble Formula) (n:nat),
Gamma_seq n Gamma Gamma'-> Included Formula Gamma Gamma'.
Proof.
    intros Gamma Gamma' n H.
    induction H. 
    -unfold Included. intros x s. apply s.
    -unfold Included. unfold Included in IHGamma_seq. intros f Hf. apply Union_introl.
    apply IHGamma_seq. apply Hf.
    -apply IHGamma_seq.
Qed. 


(*(a)*)
Lemma Gamma_seq_Cons : forall (n:nat) (Gamma Gamma_n : Ensemble Formula),
Cons Gamma -> Gamma_seq n Gamma Gamma_n -> Cons Gamma_n.
Proof.
    intros n Gamma Gamma_n H H0. induction H0.
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

(*For (b) and (c):For every n and Gamma exists Gamma_n*)
Lemma Gamma_n_exists : forall (Gamma: Ensemble Formula) (n:nat) , 
exists Gamma_n:Ensemble Formula, Gamma_seq n Gamma Gamma_n.
intros Gamma n. pose proof lem_for_consistency as H. induction n.  
+exists Gamma. apply zero. apply Gamma.
+destruct IHn. destruct H with (Gamma:=(Union Formula x (Singleton Formula (F n)))).
++exists (Union Formula x (Singleton Formula (F n))). apply consis.
+++apply H0.
+++apply H1.
++exists x. apply iconsis.
+++apply H0.
+++apply H1.
Qed.



(*This is the Definition of Gamma_star in the book! there is no need for Gamma to be consistent in this definition.
Definition of Gamma_n and Gamma_star is independent of consistency of Gamma*)
Definition Gamma_star_Def  (Gamma Gamma_star: Ensemble Formula):Prop:=
    (forall (n:nat)(Gamma_n:Ensemble Formula),
    Gamma_seq n Gamma Gamma_n -> Included Formula Gamma_n Gamma_star) 
    /\ 
    (forall f:Formula,In Formula Gamma_star f -> exists (n':nat)(Gamma_n':Ensemble Formula),Gamma_seq n' Gamma Gamma_n' /\ In Formula Gamma_n' f).


(*for the next lemma!!!:*)
Lemma Gamma_n_equality: forall (Gamma Gamma_n Gamma_n': Ensemble Formula) (n:nat),
Gamma_seq n Gamma Gamma_n -> Gamma_seq n Gamma Gamma_n' -> Gamma_n = Gamma_n'.
Admitted.

Lemma Gamma_n_increasing : forall (Gamma Gamma_n Gamma_m: Ensemble Formula) (n:nat),
Gamma_seq n Gamma Gamma_n -> Gamma_seq (S n) Gamma Gamma_m -> Included Formula Gamma_n Gamma_m.
Proof.
    intros Gamma Gamma_n Gamma_m n H0 H1.
    assert (H:Cons (Union Formula Gamma_n (Singleton Formula (F n)))  \/  ~Cons (Union Formula Gamma_n (Singleton Formula (F n)))).
    -apply lem_for_consistency.
    -destruct H.
    --apply consis in H0. 
    ---assert(H2:Gamma_m = Union Formula Gamma_n (Singleton Formula (F n))).
    ----apply Gamma_n_equality with (Gamma:=Gamma)(n:=S n).
    -----apply H1. -----apply H0.
    ----rewrite -> H2. unfold Included. intros f H9. apply Union_introl. apply H9.
    ---apply H.
    --apply iconsis in H0.
    ---assert(H2:Gamma_m = Gamma_n).
    ----apply Gamma_n_equality with (Gamma:=Gamma)(n:=S n).
    -----apply H1. -----apply H0.
    ----unfold Included. intros f H9. rewrite -> H2. apply H9.
    ---apply H.
Qed.

Lemma Gamma_n_chain : forall (Gamma Gamma' Gamma'': Ensemble Formula) (n m:nat),
Gamma_seq n Gamma Gamma' -> Gamma_seq (n+m) Gamma Gamma'' -> Included Formula Gamma' Gamma''.
intros Gamma Gamma_n Gamma_m n m H1 H2.
Admitted.


Lemma Gamma_n_weakening: forall (Gamma Gamma_n Gamma_n' : Ensemble Formula) (n m :nat) (f : Formula),
Gamma_seq n Gamma Gamma_n -> Gamma_seq (n+m) Gamma Gamma_n' -> Gamma_n |- f -> Gamma_n' |- f.
Proof.
    intros Gamma Gamma_n Gamma_n' n m f H1 H2 H3.
    assert (H4: Included Formula Gamma_n Gamma_n').
    -apply Gamma_n_chain with (Gamma:=Gamma) (n:=n) (m:=m).
    --apply H1. --apply H2. 
    -assert (H5: Gamma_n' = Union Formula Gamma_n' Gamma_n).
    --rewrite -> Union_absorbs.
    ---reflexivity.
    ---apply H4.
    --rewrite <- Union_commutative in H5. rewrite -> H5. apply Strong_Weakening. apply H3.
Qed.
    


(*for (b) again*)
Lemma Gamma_star_Prop: forall (Gamma Gamma_star:Ensemble Formula) (f:Formula),
Gamma_star_Def Gamma Gamma_star-> Gamma_star |- f ->
exists (n:nat) (Gamma_n:Ensemble Formula), Gamma_seq n Gamma Gamma_n /\
Gamma_n |- f.
intros Gamma Gamma_star f H H0.
induction H0. rename C into Gamma_star. 
+admit.
+apply IHND in H. destruct H as [n]. destruct H as [Gamma_n]. exists n. exists Gamma_n.
split. -apply H. -destruct H. apply conjE1 in H1. apply H1.
+apply IHND in H. destruct H as [n]. destruct H as [Gamma_n]. exists n. exists Gamma_n.
split. -apply H. -destruct H. apply conjE2 in H1. apply H1.
+assert (H1: Gamma_star_Def Gamma C). -apply H. -apply IHND1 in H. apply IHND2 in H1.
destruct H as [n]. destruct H as [Gamma_n]. destruct H1 as [n']. destruct H0 as [Gamma_n']. admit.
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
+Admitted.




(*(b)*)
Lemma Gamma_star_Cons: forall (Gamma Gamma_star:Ensemble Formula),
    Cons Gamma -> Gamma_star_Def Gamma Gamma_star -> Cons Gamma_star.
Proof.
    intros Gamma Gamma_star H H0 H1. apply Gamma_star_Prop with (Gamma:=Gamma) in H1.
    +destruct H1. destruct H1. destruct H1. apply prop_double_neg_I in H2. 
    pose proof Gamma_seq_Cons as H3. assert(H4: ~ Cons x0).
    ++apply H2.
    ++apply H4. apply H3 with (n:=x)(Gamma:=Gamma).
    +++apply H.
    +++apply H1.
    +apply H0.
    Qed.
    
(*(c)*)
Lemma Gamma_star_maximality :forall (Gamma Gamma_star : Ensemble Formula), 
Cons Gamma -> Gamma_star_Def Gamma Gamma_star -> forall Delta : Ensemble Formula, Cons Delta -> Included Formula Gamma_star Delta
-> Included Formula Delta Gamma_star.
Proof.
intros Gamma Gamma_star H H0 Delta H1 H2. unfold Gamma_star_Def in H0. unfold Included. intros f H4.
pose proof F_Prop_surjective as H5. destruct H5 with (f:=f). rename x into n.
pose proof Gamma_n_exists as H7. destruct H7 with (Gamma:=Gamma) (n:=n). rename x into The_Gamma.
destruct H0. assert (H9: Cons (Union Formula The_Gamma (Singleton Formula (f)))).
-apply Cons_Prop0  with (Gamma:=Delta). --apply H1. 
--unfold Included. intros f' H9. assert (H10: In Formula The_Gamma f' \/ In Formula (Singleton Formula f) f').
---apply Union_inv. apply H9.
---destruct H10. ----apply H2. apply H0 in H6. apply H6. apply H10.
----apply Singleton_inv in H10. rewrite <- H10. apply H4.
-apply consis in H6. -- rewrite <- H3. apply H0 in H6. unfold Included in H6.
apply H6. apply Union_intror. apply In_singleton.
--rewrite -> H3. apply H9.
Qed.




















