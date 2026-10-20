(** A concrete equality axiom instance at an arbitrary internal variable.
    The fixed axiom is lifted as a numeral, then instantiated internally. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
  ZFCFiniteAxiomTemplates ZFCFiniteSourceCodes NumericalZFCAxioms SourceNumeralLift
  SourceZFCProvability SourceZFCInstantiation.
Unset Implicit Arguments.

Theorem source_instantiation_diagonal M atom0 x f :
  sf_relation M SFEqual (zeroM M) (zeroM M) atom0 ->
  sf_relation M SFEqual x x f -> numerical_instantiation M atom0 x f.
Proof.
  intros H0 HX. destruct (substitution_singleton_total M x) as (b&c&HB&_).
  exists b,c. split;[exact HB|].
  apply (proj2 (numerical_substitution_equal M (zeroM M) (zeroM M) atom0 b c
    (succM M (zeroM M)) (zeroM M) f H0)).
  exists x,x. auto.
Qed.

Theorem source_zfc_reflexivity M x f :
  sf_relation M SFEqual x x f -> source_zfc_provable M f.
Proof.
  intro HF.
  set (a0:=code_numeral M (sf_make SFEqual 0 0)).
  set (ax:=code_numeral M (sf_make SFAll (sf_make SFEqual 0 0) 0)).
  assert (HA0:sf_relation M SFEqual (zeroM M) (zeroM M) a0).
  { exact (sf_make_numeral M SFEqual 0 0). }
  assert (HAX:sf_relation M SFAll a0 (zeroM M) ax).
  { exact (sf_make_numeral M SFAll (sf_make SFEqual 0 0) 0). }
  assert (HP:source_zfc_provable M ax).
  { apply source_zfc_provable_axiom. left. exists ZFCRefl.
    exact (source_formula_numeral_graph M (zfc_fixed_source ZFCRefl)). }
  exact (source_zfc_provable_all_elim M a0 ax x f HP HAX
    (source_instantiation_diagonal M a0 x f HA0 HF)).
Qed.

Print Assumptions source_instantiation_diagonal.
Print Assumptions source_zfc_reflexivity.
