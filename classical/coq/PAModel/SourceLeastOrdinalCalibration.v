(** Calibration and uniqueness of the least-ordinal goal graph. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetSchemaConstructors
  ZFCFiniteSourceCodes SourceNumeralLift SourceOrdinalPredicate SourceFiniteCutoffShift
  SourceQfFunctionality SourceLeastOrdinalGoal.
From Undecidability.FOL Require Import Syntax.Core Syntax.BinSig Sets.Signatures Sets.minZF.
From FOL Require Import FullSyntax.
Unset Implicit Arguments.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZFSignature.ZF_pred_sig | 0.

Definition least_ordinal_source (phi:sf_form) : sf_form :=
  ∃ ((source_ordinal_predicate ∧ phi) ∧
    ∀ ($0 ∈' $1 → ¬phi[source_shift_sigma 1])).

Local Opaque source_ordinal_predicate.

Theorem source_least_ordinal_functional M phi least other :
  source_least_ordinal_graph M phi least ->source_least_ordinal_graph M phi other ->least=other.
Proof.
  intros [inserted [HI HG]] [inserted' [HI' HG']].
  pose proof (source_cutoff_shift_functional M 1 phi inserted inserted' HI HI') as E.
  subst inserted'. exact (code_relation_functional M least_ordinal_expression (sf_env phi inserted)
    least other HG HG').
Qed.

Theorem source_least_ordinal_finite_lift M phi :
  source_least_ordinal_graph M (code_numeral M (sf_encode phi))
    (code_numeral M (sf_encode (least_ordinal_source phi))).
Proof.
  exists (code_numeral M (sf_encode phi[source_shift_sigma 1])). split.
  - exact (source_cutoff_shift_fixed_source M 1 (fun _=>zeroM M) phi _ _
      (source_formula_numeral_graph M phi)
      (source_formula_numeral_graph M phi[source_shift_sigma 1])).
  - pose proof (code_relation_numeral M
      (sf_env (sf_encode phi) (sf_encode phi[source_shift_sigma 1])) least_ordinal_expression) as HG.
    assert (EE:code_value (sf_env (sf_encode phi) (sf_encode phi[source_shift_sigma 1]))
      least_ordinal_expression=sf_encode (least_ordinal_source phi)).
    { unfold least_ordinal_expression,least_ordinal_source,E_sf_ex,E_sf_all,E_sf_mem.
      repeat rewrite sf_make_value. reflexivity. }
    rewrite EE in HG.
    apply (proj2 (code_relation_ext M least_ordinal_expression _ _ _
      ltac:(intros [|i];reflexivity))). exact HG.
Qed.

Print Assumptions source_least_ordinal_functional.
Print Assumptions source_least_ordinal_finite_lift.


