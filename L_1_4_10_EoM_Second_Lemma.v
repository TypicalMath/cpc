Require Import Logic_and_Set_Theory.
Require Import EoM_Zorns_Lemma.
Require Import L_1_4_10_EoM_Intro.
From Coq Require Import Powerset_facts.
From Coq Require Import Finite_sets.
From Coq Require Import Powerset_Classical_facts.
From Coq Require Import Finite_sets_facts.
From Coq Require Import Constructive_sets.

Lemma chain_subset_is_chain: forall (T A : (Ensemble (Ensemble Formula))) (Gamma : Ensemble Formula),
Included (Ensemble Formula) A T -> chain (Ensemble Formula) Inc (TheSet Gamma) T -> chain (Ensemble Formula) Inc (TheSet Gamma) A.
Proof.
    intros T A Gamma H H1. unfold chain. split. unfold chain in H1.
    +apply H1.
    +split.
    ++unfold chain in H1. destruct H1. destruct H1. 
    assert(Inc_Trans: Transitive (Ensemble (Ensemble Formula)) (Included (Ensemble Formula))).
    +++apply Inclusion_is_transitive.
    +++unfold Transitive in Inc_Trans. apply Inc_Trans with (y:=T).
    -apply H. -apply H1.
    ++intros x y H0 H2. apply H1. 
    -apply H. apply H0. -apply H. apply H2.
    Qed.

Lemma finite_chain_has_maximum:forall (T : (Ensemble (Ensemble Formula))) (Gamma : Ensemble Formula),
chain (Ensemble Formula) Inc (TheSet Gamma) T -> Finite (Ensemble Formula) T -> 
(exists (Pi : Ensemble Formula), In (Ensemble Formula) T Pi) ->
exists (max : Ensemble Formula), In (Ensemble Formula) T max /\ forall (Pi' : Ensemble Formula), In (Ensemble Formula) T Pi' -> Inc Pi' max.
intros T Gamma H H0 H1. induction H0.
+destruct H1. exists x. destruct H0.
+assert (exists (Gamma : Ensemble Formula), In (Ensemble Formula) A Gamma).
++apply Chains_Are_Nonempty with (Gamma:=Gamma). apply chain_subset_is_chain with (T:=Add (Ensemble Formula) A x).
+++unfold Included. intros f Hf. apply Union_introl. apply Hf.
+++apply H.
++destruct IHFinite.
+++apply chain_subset_is_chain with (T:=Add (Ensemble Formula) A x).
++++unfold Included. intros f Hf. apply Union_introl. apply Hf.
++++apply H.
+++apply H3. 
+++rename x0 into maxA.
assert (H5: Inc maxA x \/ Inc x maxA ).
++++apply H.
+++++apply Union_introl. apply H4.
+++++apply Union_intror. apply In_singleton.
++++destruct H5.
+++++exists x. split.
-apply Union_intror. apply In_singleton.
-intros Pi' H6. destruct H6.
--assert (H7: Inc x0 maxA).
---apply H4. apply H6.
---unfold Inc. unfold Included. intros f Hf.
apply H7 in Hf. apply H5 in Hf. apply Hf.
--apply Singleton_inv in H6. rewrite -> H6.
unfold Inc. unfold Included. intros f Hf. apply Hf.
+++++exists maxA. split.
-apply Union_introl. apply H4.
-intros Pi' H6. destruct H6. rename x0 into Pi'.
--apply H4. apply H6.
--apply Singleton_inv in H6. rewrite <- H6. apply H5.
Qed.

    
Lemma chain_finite_subset_has_maximum: forall (T D: Ensemble (Ensemble Formula)) (Gamma : Ensemble Formula),
chain (Ensemble Formula) Inc (TheSet Gamma) T -> Included (Ensemble Formula) D T -> Finite (Ensemble Formula) D -> (exists (Gamma':(Ensemble Formula)), In (Ensemble Formula) D Gamma')
->exists (max : Ensemble Formula), In (Ensemble Formula) D max /\ (forall (Pi' : Ensemble Formula), In (Ensemble Formula) D Pi' -> Inc Pi' max).
Proof.
    intros T D Gamma H H0 H1 H2. apply finite_chain_has_maximum with (Gamma := Gamma).
    +apply chain_subset_is_chain with (T:=T). 
        ++apply H0.
        ++apply H.
    +apply H1.
    +apply H2.
Qed.


Lemma first_sentence : forall (T : Ensemble (Ensemble Formula)) (Pi : Ensemble Formula),
Inc Pi (UoCE1 T) -> forall (f : Formula), In Formula Pi f -> exists (A : Ensemble Formula), In Formula A f /\ In (Ensemble Formula) T A.
Proof.
    intros T Pi HI f Hf. unfold UoCE1 in HI. unfold Inc in HI.
    unfold Included in HI. apply HI in Hf. apply About_PropUoCEl in Hf.
    unfold PropUoCE2 in Hf. destruct Hf as [A HA].
    exists A. split. apply HA. apply HA.
Qed.



(*Includers of Pi elements:*)
Definition PropIoPE (Pi : Ensemble Formula) (T : Ensemble (Ensemble Formula)) (A : Ensemble Formula) : Prop:=
In (Ensemble Formula) T A /\ (exists (f : Formula), In Formula Pi f /\ In Formula A f /\ (forall (B : Ensemble Formula), In Formula B f -> In (Ensemble Formula) T B -> Inc A B)).

Definition IoPE (Pi : Ensemble Formula) (T : Ensemble (Ensemble Formula)) : (Ensemble (Ensemble Formula)):=
PropIoPE Pi T.

Lemma About_IoPEr : forall (Pi A:Ensemble Formula) (T:Ensemble (Ensemble Formula)), 
PropIoPE Pi T A -> In (Ensemble Formula) (IoPE Pi T) A.
Proof. intros Pi A T H. apply H. 
Qed.

Lemma About_IoPEl : forall (Pi A:Ensemble Formula) (T:Ensemble (Ensemble Formula)), 
In (Ensemble Formula) (IoPE Pi T) A -> PropIoPE Pi T A.
Proof. intros f T H Q. apply Q.
Qed.

Lemma IoPE_Empty_set: forall (T : Ensemble (Ensemble Formula)), IoPE (Empty_set Formula) T = Empty_set (Ensemble Formula).
Proof. intros T. apply Extensionality_Ensembles. unfold Same_set.
split.
+unfold Included. intros X H. apply About_IoPEl in H. unfold PropIoPE in H.
destruct H. destruct H0. rename x into f. destruct H0. destruct H0.
+unfold Included. intros f H. destruct H.
Qed.

Lemma IoPE_Singleton_set:forall (T : Ensemble (Ensemble Formula)) (f : Formula) (A: Ensemble Formula),
In (Ensemble Formula)T A /\ In Formula A f /\ (forall (B:Ensemble Formula), In (Ensemble Formula) T B -> In Formula B f -> Inc A B)
->IoPE (Singleton Formula f) T = Singleton (Ensemble Formula) A.
intros T f A H. apply Extensionality_Ensembles. unfold Same_set.
split. destruct H. destruct H0.
+unfold Included. intros X H2. apply About_IoPEl in H2. unfold PropIoPE in H2.
assert (H3: X=A). destruct H2. destruct H3. destruct H3. destruct H4.
-assert (H6 : Inc X A).
--apply H5. ---apply Singleton_inv in H3. rewrite <- H3.
apply H0.
---apply H.
--assert (Inc A X).
---apply H1. ----apply H2. ----apply Singleton_inv in H3. rewrite -> H3.
apply H4.
---apply Extensionality_Ensembles. unfold Same_set. split.
----apply H6. ----apply H7.
-rewrite -> H3. apply In_singleton.
+destruct H. destruct H0. unfold Included. intros x H2.
apply About_IoPEr. unfold PropIoPE. split.
++apply Singleton_inv in H2. rewrite <- H2. apply H.
++exists f. split.
+++apply In_singleton.
+++split.
++++apply Singleton_inv in H2. rewrite <- H2. apply H0.
++++intros B H3 H4. apply Singleton_inv in H2. rewrite <- H2.
apply H1. -apply H4. -apply H3.
Qed.


Lemma Add_IoPE : forall (T : Ensemble (Ensemble Formula)) (Pi: Ensemble Formula) (f:Formula), 
~(In Formula Pi f) -> IoPE (Add Formula Pi f) T = Union (Ensemble Formula) (IoPE Pi T) (IoPE (Singleton Formula f) T).
Proof.
    intros T Pi f H.
    apply Extensionality_Ensembles. unfold Same_set. split.
    +unfold Included. unfold Add. intros A H1. apply About_IoPEl in H1.
    unfold PropIoPE in H1. destruct H1. destruct H1. destruct H1.
    apply Union_inv in H1. destruct H1.
    ++apply Union_introl. apply About_IoPEr. unfold PropIoPE.
    split.
    -apply H0. -exists x. split. --apply H1. --apply H2.
    ++apply Union_intror. apply Singleton_inv in H1. 
    rewrite ->H1 in H. 
    rewrite -> IoPE_Singleton_set with (A:=A).
    +++apply In_singleton.
    +++split.
    -apply H0.
    -split.
    --rewrite -> H1. destruct H2. apply H2.
    --intros B H3 H4. destruct H2. apply H5. 
    ---rewrite <- H1. apply H4. ---apply H3.
    +unfold Included. intros A H1. apply About_IoPEr. unfold PropIoPE.
    apply Union_inv in H1. destruct H1.
    ++split. apply About_IoPEl in H0. unfold PropIoPE in H0.
    destruct H0. destruct H1. destruct H1. destruct H2.
    +++apply H0.
    +++destruct H0. destruct H1. destruct H1. destruct H2.
    exists x. split. 
    -apply Union_introl. apply H1.
    -split. 
    --apply H2.
    --apply H3.
    ++split.
    -apply About_IoPEl in H0. unfold PropIoPE in H0.
    destruct H0. destruct H1. destruct H1. destruct H2.
    apply H0.
    -apply About_IoPEl in H0. unfold PropIoPE in H0.
    destruct H0. destruct H1. destruct H1. destruct H2.
    exists x. split.
    --apply Union_intror. apply H1.
    --split. 
    ---apply H2.
    ---apply H3.
    Qed.

    


Lemma Union_finite_but_not_add : forall (U : Type) (A : Ensemble U) (x : U),
Finite U A -> ~ In U A x -> Finite U (Union U A (Singleton U (x))).
intros U A x H H3.
assert (H1: Union U A (Singleton U x) = Add U A x).
+apply Extensionality_Ensembles. unfold Same_set.
split.
++unfold Included. intros u Hu. unfold Add. apply Hu.
++unfold Included. intros u Hu. unfold Add in Hu. apply Hu.
+rewrite -> H1. apply Union_is_finite.
-apply H.
-apply H3.
Qed.





Lemma chain_has_minimum: forall (T : Ensemble(Ensemble Formula)) (Gamma : Ensemble Formula),
chain (Ensemble Formula) Inc (TheSet Gamma) T -> exists (min : Ensemble Formula), In (Ensemble Formula) T min /\ forall (A : Ensemble Formula), In (Ensemble Formula) T A -> Inc min A.
Proof.
intros T Gamma H. unfold chain in H.
Admitted.


Lemma chain_with_certain_formula_has_minimum: forall (T: Ensemble (Ensemble Formula)) (f : Formula),
In Formula (UoCE1 T) f -> exists (A : Ensemble Formula),forall (B : Ensemble Formula), In Formula B f -> Inc A B.
Proof.
Admitted.    




Lemma IoPE_is_not_empty :forall (T : Ensemble (Ensemble Formula)) (Pi : Ensemble Formula),
(exists f : Formula, In Formula Pi f /\ In Formula (UoCE1 T) f) -> exists (A : Ensemble Formula), In (Ensemble Formula) (IoPE Pi T) A.
Proof.
    Admitted.
  






Lemma second_sentence : forall (T : Ensemble (Ensemble Formula)) (Pi : Ensemble Formula),
Finite Formula Pi -> Inc Pi (UoCE1 T) -> Finite (Ensemble Formula) (IoPE Pi T).
intros T Pi H H1.

induction H. 
+rewrite IoPE_Empty_set. apply Empty_is_finite.

+rewrite -> Add_IoPE. rename A into Pi'.
++apply Union_preserves_Finite.
+++apply IHFinite. unfold Add in H1.
unfold Inc in H1. unfold Inc. unfold Included. unfold Included in H1.
intros f Hf. apply H1. apply Union_introl. apply Hf.
+++assert (H2: exists (A:Ensemble Formula), In (Ensemble Formula) T A /\ In Formula A x /\ forall (B: Ensemble Formula), In (Ensemble Formula) T B -> In Formula B x -> Inc A B).
++++ 











++++destruct H2. rename x0 into A. rewrite -> IoPE_Singleton_set with (A:=A).
+++++apply Singleton_is_finite.
+++++split. apply H2. split. -destruct H2. destruct H3. apply H3.
-destruct H2. destruct H3. apply H4.
++apply H0.
Qed.




















Lemma UoCE1_has_subset : forall (T : Ensemble (Ensemble Formula)) (Gamma Pi: Ensemble Formula),
chain (Ensemble Formula) Inc (TheSet Gamma) T /\ Inc Pi (UoCE1 T) /\ Finite Formula Pi /\ (exists (f:Formula), In Formula Pi f)
-> exists Pi', In (Ensemble Formula) T Pi' /\ Inc Pi Pi'.
Proof. intros T Gamma Pi H.    
Admitted.
