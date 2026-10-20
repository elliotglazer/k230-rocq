(** Actual internal Hilbert proofs of equality laws. All variable indices
    are arbitrary PA-model elements. Reflexivity chooses the model successor
    as its distinct auxiliary index. No completeness theorem is used. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  CodeDescent NumericalProofs ProofTemplates TemplateCD TemplatePropositional
  ProofMacros QuantifierMacros EqualityMacros KInternalLogic.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.

Lemma expression_equality_graph M rho X Y x y f :
  code_relation M rho X x -> code_relation M rho Y y ->
  (code_relation M rho (E_weq X Y) f <-> equality_graph M x y f).
Proof.
  intros HX HY.
  unfold E_weq,E_wim,equality_graph,tagged_pair_graph. cbn [code_relation]. split.
  - intros [q [r [[four [p [Hfour [[a [b [Ha [Hb Hp]]]] Hq]]]] [Hr Hf]]]].
    assert (a=x) by exact (code_relation_functional M X rho a x Ha HX).
    assert (b=y) by exact (code_relation_functional M Y rho b y Hb HY).
    subst a b four r q. now exists p.
  - intros [p [Hp Hf]].
    exists (mulM M (code_numeral M 4) p),(code_numeral M 3).
    split; [|auto]. exists (code_numeral M 4),p.
    split; [reflexivity|]. split; [exists x,y; auto|reflexivity].
Qed.

Lemma equality_successor_distinct M x : succM M x <> x.
Proof.
  intro H. apply (@Peano.lt_neq (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) x (succM M x) (coding_lt_succ M x)).
  now symmetry.
Qed.

Theorem numerical_equality_reflexivity M x f :
  equality_graph M x x f -> numerically_provable M f.
Proof.
  intro Hf. set (z := succM M x).
  set (rho := code_parameters x x z (zeroM M)).
  assert (Hguard : template_guards_hold M rho K_parameter_guards).
  { apply K_parameter_guards_correct; apply equality_successor_distinct. }
  assert (Hex : code_relation M rho (E_weq (CEvar 0) (CEvar 0)) f).
  { apply (proj2 (expression_equality_graph M rho (CEvar 0) (CEvar 0) x x f
      eq_refl eq_refl)). exact Hf. }
  eapply (proof_macro_sound M rho K_parameter_guards (@nil code_expr)
    (E_weq (CEvar 0) (CEvar 0)) Hguard).
  - intros e H. inversion H.
  - apply (macro_eq_refl K_parameter_guards (@nil code_expr) (CEvar 0) (CEvar 2)).
    unfold K_parameter_guards. now left.
  - exact Hex.
Qed.

Lemma numerical_expression_reflexivity M rho X x f :
  code_relation M rho X x -> code_relation M rho (E_weq X X) f ->
  numerically_provable M f.
Proof.
  intros HX Hf. apply (numerical_equality_reflexivity M x f).
  exact (proj1 (expression_equality_graph M rho X X x x f HX HX) Hf).
Qed.

Definition E_eq_symmetry x y := E_wim (E_weq x y) (E_weq y x).
Definition E_eq_transitivity x y z :=
  E_wim (E_weq x y) (E_wim (E_weq y z) (E_weq x z)).
Definition E_eq_transport u u' v v' :=
  E_wim (E_weq u u') (E_wim (E_weq v v') (E_wim (E_weq u v) (E_weq u' v'))).
Definition E_member_transport u u' v v' :=
  E_wim (E_weq u u') (E_wim (E_weq v v') (E_wim (E_wel u v) (E_wel u' v'))).

Theorem numerical_equality_symmetry M x y f :
  code_relation M (code_parameters x y (zeroM M) (zeroM M))
    (E_eq_symmetry (CEvar 0) (CEvar 1)) f -> numerically_provable M f.
Proof.
  intro Hf. set (rho := code_parameters x y (zeroM M) (zeroM M)).
  destruct (code_relation_total M (E_weq (CEvar 0) (CEvar 0)) rho) as [r Hr].
  assert (Hpr : numerically_provable M r).
  { exact (numerical_expression_reflexivity M rho (CEvar 0) x r eq_refl Hr). }
  apply (unguarded_macro_sound M rho (cons (E_weq (CEvar 0) (CEvar 0)) nil)
    (E_eq_symmetry (CEvar 0) (CEvar 1))
    (macro_one_input M rho _ r Hr Hpr)).
  - unfold E_eq_symmetry. apply macro_eq_sym.
    apply PM_input. now left.
  - exact Hf.
Qed.

Theorem numerical_equality_transitivity M x y z f :
  code_relation M (code_parameters x y z (zeroM M))
    (E_eq_transitivity (CEvar 0) (CEvar 1) (CEvar 2)) f -> numerically_provable M f.
Proof.
  intro Hf. set (rho := code_parameters x y z (zeroM M)).
  destruct (code_relation_total M (E_weq (CEvar 0) (CEvar 0)) rho) as [r Hr].
  assert (Hpr : numerically_provable M r).
  { exact (numerical_expression_reflexivity M rho (CEvar 0) x r eq_refl Hr). }
  apply (unguarded_macro_sound M rho (cons (E_weq (CEvar 0) (CEvar 0)) nil)
    (E_eq_transitivity (CEvar 0) (CEvar 1) (CEvar 2))
    (macro_one_input M rho _ r Hr Hpr)).
  - unfold E_eq_transitivity. apply macro_eq_trans.
    apply PM_input. now left.
  - exact Hf.
Qed.

Theorem numerical_equality_transport M u u' v v' f :
  code_relation M (code_parameters u u' v v')
    (E_eq_transport (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) f ->
  numerically_provable M f.
Proof.
  intro Hf. set (rho := code_parameters u u' v v').
  destruct (code_relation_total M (E_weq (CEvar 1) (CEvar 1)) rho) as [r Hr].
  assert (Hpr : numerically_provable M r).
  { exact (numerical_expression_reflexivity M rho (CEvar 1) u' r eq_refl Hr). }
  apply (unguarded_macro_sound M rho (cons (E_weq (CEvar 1) (CEvar 1)) nil)
    (E_eq_transport (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3))
    (macro_one_input M rho _ r Hr Hpr)).
  - unfold E_eq_transport. apply macro_eq_transport.
    apply PM_input. now left.
  - exact Hf.
Qed.

Theorem numerical_membership_transport M u u' v v' f :
  code_relation M (code_parameters u u' v v')
    (E_member_transport (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)) f ->
  numerically_provable M f.
Proof.
  intro Hf. apply (unguarded_macro_sound M (code_parameters u u' v v') (@nil code_expr)
    (E_member_transport (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3))).
  - intros e H. inversion H.
  - unfold E_member_transport. apply macro_member_transport.
  - exact Hf.
Qed.

Print Assumptions numerical_equality_reflexivity.
Print Assumptions numerical_equality_symmetry.
Print Assumptions numerical_equality_transitivity.
Print Assumptions numerical_equality_transport.
Print Assumptions numerical_membership_transport.
