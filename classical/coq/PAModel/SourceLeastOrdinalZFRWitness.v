(** Uniform ZFR least-witness implication. The actual schematic Separation
    proof and all three finite set-theory certificates are supplied here;
    no axiom-image, minimum, or proof-transformer premise is retained. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SourceBounded NumericalSourceFull SourceFiniteCutoffShift
  SourceOrdinalPredicate SourceLeastOrdinalGoal SourceLeastOrdinalFixed
  SourceZFRSeparationZero SourceSeparationZeroSpecialization SourceLeastOrdinalWitness
  SourceSetTheoryDescriptors SourceDescriptorProvability SourceZFRProvability
  SourceFiniteProofContexts.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_ordinal_predicate source_ordinal_predicate_code.

Theorem source_zfr_least_ordinal_witness M phi p1 target count body implication :
  source_bounded M phi (succM M count) ->source_cutoff_shift M 1 phi p1 ->
  source_least_ordinal_graph M p1 target ->
  sf_relation M SFAnd (source_ordinal_predicate_code M) phi body ->
  sf_relation M SFImpl body target implication ->source_zfr_provable M implication.
Proof.
  intros HB HP1 HG HBody HImp.
  destruct (source_cutoff_shift_total M 1 p1) as (p2&HP2).
  destruct (source_cutoff_shift_total M 1 p2) as (p3&HP3).
  pose proof (source_cutoff_shift_bounded M 1 phi p1 count HB HP1) as HB1.
  pose proof (source_cutoff_shift_bounded M 1 p1 p2 (succM M count) HB1 HP2) as HB2.
  destruct (source_zfr_separation_zero_total M p2 (succM M (succM M count)) p3 HB2 HP3)
    as (specialized&HSep&PSep).
  destruct (code_relation_total M (least_fixed_parameter_expression LeastSuccessorContainer)
    (fun _=>zeroM M)) as (successorlaw&HSuc).
  destruct (code_relation_total M (least_fixed_parameter_expression LeastOrdinalMember)
    (fun _=>code_numeral M 1)) as (ordinallaw&HOrd).
  destruct (code_relation_total M (least_fixed_parameter_expression LeastRegularMinimum)
    (schema_env3 (zeroM M) (code_numeral M 2) (zeroM M))) as (regularlaw&HReg).
  pose proof (source_zfr_least_fixed_parameters M LeastSuccessorContainer _ successorlaw HSuc) as PSuc.
  pose proof (source_zfr_least_fixed_parameters M LeastOrdinalMember _ ordinallaw HOrd) as POrd.
  pose proof (source_zfr_least_fixed_parameters M LeastRegularMinimum _ regularlaw HReg) as PReg.
  assert (Premises:forall f,In f [successorlaw;ordinallaw;regularlaw;specialized] ->
    source_descriptor_provable M ZFRSourceDescriptor f).
  { intros f [<-|[<-|[<-|[<-|[]]]]];
      apply (proj2 (source_zfr_descriptor_provable M _));assumption. }
  destruct (source_descriptor_finite_common_context M ZFRSourceDescriptor _ Premises)
    as (b&c&n&HC&P).
  exists b,c,n. split;[exact (proj1 (source_zfr_descriptor_context M b c n) HC)|].
  apply (source_full_least_ordinal_witness M b c n count phi p1 p2 p3 successorlaw ordinallaw
    regularlaw specialized body implication target);try assumption.
  - exact (proj1 HC).
  - apply P. cbn;tauto.
  - apply P. cbn;tauto.
  - apply P. cbn;tauto.
  - apply P. cbn;tauto.
Qed.

Print Assumptions source_zfr_least_ordinal_witness.
