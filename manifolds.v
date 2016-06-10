Require Import Coq.Program.Basics.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Image.
Require Import Coquelicot.Coquelicot.

Implicit Arguments In [U].
Implicit Arguments Intersection [U].
Implicit Arguments Union [U].
Implicit Arguments Singleton [U].
Implicit Arguments Image.Im [U V].
Implicit Arguments injective [U V].

Section Sets.

Context {U: Type} {V: Type}.

Lemma Im_singleton: forall (x: U) (f: U->V), Image.Im (Singleton x) f = Singleton (f x).
Proof.
  intros x f.
  apply Extensionality_Ensembles.
  unfold Same_set, Included.
  split.

    intros x0 in_image_singleton.
    case in_image_singleton.
    intros x1 in_singleton y y_eq_f_x1.
    induction in_singleton.
    auto with sets.

    intros x0 x0_in_singleton.
    induction x0_in_singleton.
    auto with sets.
Qed.

Lemma Im_id: forall (S: Ensemble U), Image.Im S (fun x: U => x) = S.
Proof.
  intro S.
  apply Extensionality_Ensembles.
  unfold Same_set, Included.
  split.
    intros x in_image_x.
    case in_image_x.
    intros x0 in_s_x0 y y_eq_x0.
    rewrite y_eq_x0.
    trivial.
   
    intros.
    apply Im_intro with (x:=x); auto.
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



(*
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