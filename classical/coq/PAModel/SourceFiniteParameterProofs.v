(** Specialize a fixed finite source theorem to arbitrary internal variable
    names, using a real three-entry numerical renaming map. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions
  SetFormulaCodes SourceFiniteContexts FixedSourceBounds SourceNumeralLift
  NumericalRenamingMaps ThreeNameRenaming NumericalTheories SourceDescriptorProvability
  SourceDescriptorClosure SourceFiniteParameters.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition source_three_parameter_names i :=
  match i with 0=>CEvar 0 | 1=>CEvar 1 | 2=>CEvar 2 | S(S(S j))=>CEconst (S(S(S j))) end.

Theorem source_descriptor_parameter_proof M T phi names rho b c n delta out :
  source_descriptor_provable M T (code_numeral M (sf_encode phi)) ->
  (forall i x,code_relation M rho (names i) x ->
    renaming_lookup M b c n delta (code_numeral M i) x) ->
  code_relation M rho (source_parameter_expression names phi) out ->
  source_descriptor_provable M T out.
Proof.
  intros HP HL HO. apply (source_descriptor_provable_renaming M T
    (code_numeral M (sf_encode phi)) b c n delta out HP).
  exact (source_finite_parameter_renaming M phi names rho b c n delta out HL HO).
Qed.

Theorem source_descriptor_three_parameter_proof M T phi rho out :
  source_descriptor_provable M T (code_numeral M (sf_encode phi)) ->
  code_relation M rho (source_parameter_expression source_three_parameter_names phi) out ->
  source_descriptor_provable M T out.
Proof.
  intros HP HO.
  destruct (three_name_renaming_total M (rho 0) (rho 1) (rho 2) (zeroM M))
    as (b&c&H0&H1&H2).
  apply (source_descriptor_parameter_proof M T phi source_three_parameter_names rho
    b c (code_numeral M 3) (zeroM M) out HP);[|exact HO].
  intros [|[|[|i]]] x HX;cbn [source_three_parameter_names] in HX.
  - change (x=rho 0) in HX. now subst x.
  - change (x=rho 1) in HX. now subst x.
  - change (x=rho 2) in HX. now subst x.
  - change (x=code_numeral M (S(S(S i)))) in HX. subst x.
    assert (HOutside:~coding_lt M (code_numeral M (S(S(S i)))) (code_numeral M 3)).
    { intro HBad. apply (proj1 (fixed_source_numeral_lt_iff M (S(S(S i))) 3)) in HBad. lia. }
    apply (proj2 (renaming_lookup_outside M b c (code_numeral M 3) (zeroM M)
      (code_numeral M (S(S(S i)))) (code_numeral M (S(S(S i)))) HOutside)).
    symmetry. apply coding_add_zero_r.
Qed.

Print Assumptions source_descriptor_parameter_proof.
Print Assumptions source_descriptor_three_parameter_proof.

