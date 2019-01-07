Require Import Classical.
Require Import FunctionalExtensionality.

Section Sets.

Definition Ensemble (U: Type) := U -> Prop.

Definition Singleton {U: Type} (x: U): Ensemble U := fun u: U => u = x.

Definition In {U: Type} (X: Ensemble U) (x: U) : Prop := X x.

Definition Im {U V: Type} (X: Ensemble U) (f: U -> V): Ensemble V := fun v: V => exists u: U, In X u /\ f u = v.

Axiom set_extensionality : forall  {U: Type} (X Y: Ensemble U), X=Y <-> (forall u: U, In X u <-> In Y u).

Axiom prop_extensionality: ClassicalFacts.prop_extensionality.

Hint Unfold In Singleton Im: sets.

Print ClassicalFacts.prop_extensionality.

Lemma Im_singleton {U V: Type}: forall (u: U) (f: U -> V), Im (Singleton u) f = Singleton (f u).
Proof.
  repeat autounfold with sets.
  intuition.
  extensionality w.
  apply prop_extensionality.
  intuition.
  repeat destruct H.  
    exact (eq_sym H0).
  eauto.
Qed.


Lemma Im_singleton2 {U V: Type}: forall (u: U) (f: U -> V), Im (Singleton u) f = Singleton (f u).
Proof.
  intros u f.
  extensionality w.
  apply prop_extensionality.
  repeat autounfold with sets.
  split ;   intro H.
    repeat destruct H.  
    exact (eq_sym H0).

    eauto.
Qed.


Lemma Im_id: forall {U: Type} (S: Ensemble U), Im S (fun x: U => x) = S.
Proof.
  intros U S.
  apply set_extensionality.
  repeat autounfold with sets.
  split; intro H.
    repeat destruct H.
    rewrite <- H0.
    assumption.

    eauto.
Qed.

Lemma Full_set_true: Full_set U = (fun x: U => True).
Proof.
  apply Extensionality_Ensembles.
  unfold Same_set, Included.
  split; [ auto with sets | intros; apply Full_intro].
Qed.

Definition injective_on (f: U -> V) (A: Ensemble U) := 
  forall x1:U, forall x2:U, In A x1 /\ In A x2 /\ (f x1 = f x2) -> x1 = x2.

Definition surjective_on (f: U -> V) (B: Ensemble V) := 
  forall y:V, In B y -> exists x: U, f(x)=y.

Definition bijective_on (f: U -> V) (A: Ensemble U) (B: Ensemble V) := 
  injective_on f A /\ surjective_on f B.

Definition inverse_on (f:U -> V) (A: Ensemble U) (B: Ensemble V) (g: V -> U) :=
  (forall x:U, In A x -> g (f x) = x) /\
  (forall y:V, In B y -> f (g y) = y) .

Lemma injective_impl_injective_on: forall (f: U -> V) (A: Ensemble U), injective f -> injective_on f A.
Proof.
  intros f a inj_f.
  unfold injective_on.
  unfold injective in inj_f.
  intros x1 x2 H.
  destruct H as [H1 H].
  destruct H as [H2 H3].
  apply inj_f.
  trivial.
Qed.

End Sets.

(** Families has been copied by ZornsLemma.Families **)

Section Families.

Context { T:Type }.

Definition Family := Ensemble (Ensemble T).

Inductive FamilyUnion (F: Family): Ensemble T :=
  | family_union_intro: forall (S:Ensemble T) (x:T),
    In F S -> In S x -> In (FamilyUnion F) x.

Inductive FamilyIntersection (F: Family): Ensemble T :=
  | family_intersection_intro: forall x:T,
    (forall S:Ensemble T, In F S -> In S x) ->
    In (FamilyIntersection F) x.

Lemma family_union_singleton: forall S: Ensemble T, FamilyUnion (Singleton S) = S.
Proof.
  intro S.
  apply Extensionality_Ensembles.
  unfold Same_set, Included.
  split.
    intros x in_fam_x.
    induction in_fam_x as [S0 x0 in_sing_s0 in_s0_x0].
    induction in_sing_s0.
    assumption.

    intros x in_s_x.
    apply family_union_intro with (S:=S); auto with sets.
Qed.

End Families.

(** Some definitions localized on a particular subdomain **)


Definition ex_filterdiff_on {K: AbsRing} {S T: NormedModule K} (f: S-> T) (U: Ensemble S) :=
  forall x: S,  In U x -> ex_filterdiff f (locally x).

(** Manifols **)

Section Manifold.

Context {K: AbsRing} {S: NormedModule K} {T: Type} {X: Ensemble T}.

Print Image.Im.

Record Chart: Type := mkChart {
  dom: Ensemble T;
  phi: T -> S;
  cod := Image.Im dom phi;
  phi_image_open: open cod;
  (* phi_injective: injective _ _ (fun x: { p | In U p} => phi (proj1_sig x)) *)
  phi_injective: injective_on phi dom
}.

Record Atlas: Type := mkAtlas {
  charts: Ensemble Chart;
  total_cover: FamilyUnion (Image.Im charts (fun chart => (dom chart))) = X;
  open_intersection: 
    forall chart1 chart2, In charts chart1 /\ In charts chart2 -> open(Image.Im (Intersection (dom chart1) (dom chart2)) (phi chart1));
  differentiable_comps: 
    forall chart1 chart2, forall x: T,
      let phi1 := phi chart1 in
      let phi2 := phi chart2 in
      let chart_intersection := Intersection (dom chart1) (dom chart2) in
      let dom1 := Image.Im chart_intersection phi1 in 
      let dom2 := Image.Im chart_intersection phi2 in
      forall g: S -> T, inverse_on phi1 (dom chart1) (cod chart1) g -> ex_filterdiff_on (compose phi2 g) dom1
}.
End Manifold.

Section RManifold.
  Let Rset := Full_set R.

  Let id_Rset := id(A:=R).

  Let id_Rset_image_open: open (Image.Im Rset id_Rset).
  Proof.
    rewrite Im_id.
    unfold Rset.
    rewrite Full_set_true.
    exact open_true.
  Qed.

  Let id_Rset_injective: injective_on id_Rset Rset.
  Proof.
    apply injective_impl_injective_on.
    unfold injective.
    auto.
  Qed.

  Definition RChart := mkChart Rset id_Rset id_Rset_image_open id_Rset_injective.

  Let charts := Singleton RChart.

  Theorem c_total_cover: (FamilyUnion(Image.Im charts (fun chart => (dom chart)))) = Rset.
  Proof.
    unfold charts.
    rewrite Im_singleton.
    rewrite family_union_singleton.
    trivial.
  Qed.

End RManifold.

(**
Require Import Logic.ClassicalEpsilon.

Definition inverse {X Y:Type} (f:X->Y) (U: Ensemble X) (V: Ensemble Y) (inj: injective_on f U) (i: inhabited X) := 
  fun y: Y => epsilon i (fun x: X => f x = y).

Lemma inverse_is_inverse: forall (X Y:Type) (f:X->Y) (U: Ensemble X) (V: Ensemble Y) (inj: injective_on f U) (i: inhabited X), inverse_on f U V (inverse f U V inj i).
Proof.
  intros.
  unfold inverse.
  unfold inverse_on.
Qed.
**)
