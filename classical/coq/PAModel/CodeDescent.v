(** Structural induction for the exact numerical formula encoding, inside
    any PA model. Recursive subformulas strictly decrease even when their
    codes are nonstandard. This is not external induction over parsed terms. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT
  FiniteCRTFormula Pairing CodeExpressions NumericalProofs CourseOfValues.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia setoid_ring.Ring.
Unset Implicit Arguments.

Definition tagged_pair_graph M tag a b f := exists p,
  pair_graph M a b p /\
  f = addM M (mulM M (code_numeral M 4) p) (code_numeral M tag).

Definition membership_graph M := tagged_pair_graph M 1.
Definition equality_graph M := tagged_pair_graph M 3.

Lemma implication_graph_tagged M a b f :
  implication_graph M a b f <-> tagged_pair_graph M 0 a b f.
Proof.
  unfold implication_graph,E_wim. cbn [code_relation]. split.
  - intros [four [p [Hfour [[x [y [Hx [Hy Hp]]]] Hf]]]].
    change (x=a) in Hx. change (y=b) in Hy. subst x y four.
    exists p. split; [exact Hp|].
    change (f=mulM M (code_numeral M 4) p) in Hf.
    rewrite (coding_add_zero_r M). exact Hf.
  - intros [p [Hp Hf]]. exists (code_numeral M 4),p.
    split; [reflexivity|]. split.
    + exists a,b. repeat split; try reflexivity. exact Hp.
    + change (f=mulM M (code_numeral M 4) p).
      now rewrite (coding_add_zero_r M) in Hf.
Qed.

Lemma universal_graph_tagged M a b f :
  universal_graph M a b f <-> tagged_pair_graph M 2 a b f.
Proof.
  change ((exists q r, implication_graph M a b q /\
    r=code_numeral M 2 /\ f=addM M q r) <-> tagged_pair_graph M 2 a b f).
  split.
  - intros [q [r [Hq [Hr Hf]]]]. subst r.
    apply implication_graph_tagged in Hq. destruct Hq as [p [Hp Hq]].
    change (q=addM M (mulM M (code_numeral M 4) p) (zeroM M)) in Hq.
    rewrite (coding_add_zero_r M) in Hq. exists p.
    split; [exact Hp|]. now rewrite Hq in Hf.
  - intros [p [Hp Hf]]. exists (mulM M (code_numeral M 4) p),(code_numeral M 2).
    split; [|auto]. apply implication_graph_tagged. exists p.
    split; [exact Hp|]. symmetry. apply coding_add_zero_r.
Qed.

Section Descent.
Variable M : Model.
Local Notation D := (carrier M).
Local Notation O := (zeroM M).
Local Notation S := (succM M).
Local Infix "+" := (addM M).
Local Infix "*" := (mulM M).
Local Notation N := (code_numeral M).
Add Ring descent_ring : (model_semiring M).

Lemma triangular_large s : exists t d, triangular_graph M s t /\ t = s+d.
Proof.
  apply (definable_induction M (fun s => exists t d,
    triangular_graph M s t /\ t=s+d)).
  - exists (∃∃ ((num 2 ⊗ $1 == $2 ⊗ σ $2) ∧ ($1 == $2 ⊕ $0))),
      (fun _ => O).
    intro x. reflexivity.
  - exists O,O. unfold triangular_graph. split; ring.
  - intros n [t [d [Ht Et]]]. exists (t+S n),(d+n).
    split.
    + unfold triangular_graph in *.
      replace (twoM M * (t+S n)) with (twoM M*t+twoM M*S n) by ring.
      rewrite Ht. symmetry. apply consecutive_product_step.
    + rewrite Et, (succ_as_add M n). ring.
Qed.

Lemma pair_coordinate_bounds a b p : pair_graph M a b p ->
  (exists d, p=a+d) /\ (exists d, p=b+d).
Proof.
  intro Hp. destruct (triangular_large (a+b)) as [t [d [Ht Et]]].
  assert (Ep : p=t+b).
  { apply (double_cancel M). unfold pair_graph in Hp.
    unfold triangular_graph in Ht.
    replace (twoM M*(t+b)) with (twoM M*t+twoM M*b) by ring.
    now rewrite Ht. }
  rewrite Ep,Et. split.
  - exists (b+d+b). ring.
  - exists (a+b+d). ring.
Qed.

Lemma tagged_pair_positive_descent a b f tag : tag <> 0 ->
  tagged_pair_graph M tag a b f -> coding_lt M a f /\ coding_lt M b f.
Proof.
  intros Htag [p [Hp Ef]]. destruct tag as [|tag]; [contradiction|].
  destruct (pair_coordinate_bounds a b p Hp) as [[d Ed] [e Ee]].
  change (f=N 4*p+S (N tag)) in Ef.
  assert (Efour : N 4 = S O+S O+S O+S O).
  { cbn [code_numeral]. rewrite (succ_as_add M (S (S (S O)))),
      (succ_as_add M (S (S O))), (succ_as_add M (S O)). ring. }
  split.
  - exists (d+p+p+p+N tag). rewrite Ef,Efour,(succ_as_add M (N tag)),Ed.
    rewrite (succ_as_add M (a+(d+(a+d)+(a+d)+(a+d)+N tag))). ring.
  - exists (e+p+p+p+N tag). rewrite Ef,Efour,(succ_as_add M (N tag)),Ee.
    rewrite (succ_as_add M (b+(e+(b+e)+(b+e)+(b+e)+N tag))). ring.
Qed.

Lemma tagged_pair_zero_descent a b f : f <> O ->
  tagged_pair_graph M 0 a b f -> coding_lt M a f /\ coding_lt M b f.
Proof.
  intros Hf [p [Hp Ef]].
  destruct (@Peano.zero_or_succ D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) p) as [Ep|[k Ep]].
  - subst p. exfalso. apply Hf. rewrite Ef.
    change (N 4*O+O=O). ring.
  - destruct (pair_coordinate_bounds a b p Hp) as [[d Ed] [e Ee]].
    assert (Efour : N 4 = S O+S O+S O+S O).
    { cbn [code_numeral]. rewrite (succ_as_add M (S (S (S O)))),
        (succ_as_add M (S (S O))), (succ_as_add M (S O)). ring. }
    change (f=N 4*p+O) in Ef.
    split.
    + exists (d+k+k+k+N 2). rewrite Ef,Efour.
      replace ((S O+S O+S O+S O)*p+O) with (p+p+p+p) by ring.
      rewrite Ed at 1. rewrite Ep.
      change ((a+d)+S k+S k+S k = S (a+(d+k+k+k+S (S O)))).
      rewrite (succ_as_add M k), (succ_as_add M (S O)),
        (succ_as_add M (a+(d+k+k+k+(S O+S O)))). ring.
    + exists (e+k+k+k+N 2). rewrite Ef,Efour.
      replace ((S O+S O+S O+S O)*p+O) with (p+p+p+p) by ring.
      rewrite Ee at 1. rewrite Ep.
      change ((b+e)+S k+S k+S k = S (b+(e+k+k+k+S (S O)))).
      rewrite (succ_as_add M k), (succ_as_add M (S O)),
        (succ_as_add M (b+(e+k+k+k+(S O+S O)))). ring.
Qed.

Lemma numeral_inu n : @Peano.inu D (raw_interpretation M) n = N n.
Proof. induction n; [reflexivity|]. change (S (@Peano.inu D (raw_interpretation M) n)=S (N n)). now rewrite IHn. Qed.

Lemma formula_code_cases f :
  (exists a b, tagged_pair_graph M 0 a b f) \/
  (exists a b, membership_graph M a b f) \/
  (exists a b, tagged_pair_graph M 2 a b f) \/
  (exists a b, equality_graph M a b f).
Proof.
  destruct (@Peano.iEuclid' D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) f 4 ltac:(lia)) as [q [r [Hr Hf]]].
  rewrite !numeral_inu in Hf.
  destruct (pair_surjective M q) as [a [b Hp]].
  assert (Htag : tagged_pair_graph M r a b f).
  { exists q. split; [exact Hp|]. rewrite Hf.
    change (q*N 4+N r=N 4*q+N r). ring. }
  destruct r as [|[|[|[|r]]]]; try lia.
  - left. now exists a,b.
  - right; left. now exists a,b.
  - right; right; left. now exists a,b.
  - right; right; right. now exists a,b.
Qed.

Theorem formula_code_induction (P : D -> Prop) :
  Definable1 M P -> P O ->
  (forall a b f, membership_graph M a b f -> P f) ->
  (forall a b f, equality_graph M a b f -> P f) ->
  (forall a b f, f <> O -> tagged_pair_graph M 0 a b f -> P a -> P b -> P f) ->
  (forall a b f, tagged_pair_graph M 2 a b f -> P b -> P f) ->
  forall f, P f.
Proof.
  intros HD Hzero Hmem Heq Himp Hall.
  apply (definable_strong_induction M P HD). intros f IH.
  destruct (@Peano.D_eq_dec D (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) f O) as [->|Hnonzero]; [exact Hzero|].
  destruct (formula_code_cases f) as [[a [b H]]|[[a [b H]]|[[a [b H]]|[a [b H]]]]].
  - destruct (tagged_pair_zero_descent a b f Hnonzero H) as [Ha Hb].
    exact (Himp a b f Hnonzero H (IH a Ha) (IH b Hb)).
  - exact (Hmem a b f H).
  - destruct (tagged_pair_positive_descent a b f 2 ltac:(lia) H) as [_ Hb].
    exact (Hall a b f H (IH b Hb)).
  - exact (Heq a b f H).
Qed.

Corollary named_formula_code_induction (P : D -> Prop) :
  Definable1 M P -> P O ->
  (forall a b f, membership_graph M a b f -> P f) ->
  (forall a b f, equality_graph M a b f -> P f) ->
  (forall a b f, f <> O -> implication_graph M a b f -> P a -> P b -> P f) ->
  (forall a b f, universal_graph M a b f -> P b -> P f) ->
  forall f, P f.
Proof.
  intros HD Hzero Hmem Heq Himp Hall.
  apply (formula_code_induction P HD Hzero Hmem Heq).
  - intros a b f Hnz Hf Ha Hb. apply (Himp a b f Hnz); try assumption.
    now apply implication_graph_tagged.
  - intros a b f Hf Hb. apply (Hall a b f); [|exact Hb].
    now apply universal_graph_tagged.
Qed.

End Descent.

Print Assumptions pair_coordinate_bounds.
Print Assumptions formula_code_cases.
Print Assumptions formula_code_induction.
