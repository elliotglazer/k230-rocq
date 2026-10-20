(** A genuine Separation proof specialized to an arbitrary model-valued container name, uniformly
    for arbitrary internal matrices and parameter-closure lengths. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded SourceFiniteCutoffShift SourceSetTheoryDescriptors SourceZFRProvability
  SourceZFRSeparationUse SourceDescriptorInstantiation SourceSeparationContainerSpecialization.
Unset Implicit Arguments.

Theorem source_zfr_separation_container_total M phi count p1 A :
  source_bounded M phi (succM M count) -> source_cutoff_shift M 1 phi p1 ->
  exists specialized,
    code_relation M (source_separation_container_environment M A p1)(E_separation_container(CEvar 0)(CEvar 1)) specialized /\
    source_zfr_provable M specialized.
Proof.
  intros HB HP.
  destruct (source_zfr_separation_open_total M phi count HB) as (body&raw&HBody&HRaw&PRaw).
  destruct (source_separation_container_specialization M phi body raw p1 (succM M count) A
    HB HBody HRaw HP) as (rawbody&specialized&HAll&HInst&HGraph).
  exists specialized. split;[exact HGraph|].
  apply (proj1 (source_zfr_descriptor_provable M specialized)).
  apply (source_descriptor_provable_all_elim M ZFRSourceDescriptor rawbody raw
    A specialized);[|exact HAll|exact HInst].
  exact (proj2 (source_zfr_descriptor_provable M raw) PRaw).
Qed.

Theorem source_zfr_separation_container M phi count p1 A specialized :
  source_bounded M phi (succM M count) -> source_cutoff_shift M 1 phi p1 ->
  code_relation M (source_separation_container_environment M A p1)(E_separation_container(CEvar 0)(CEvar 1)) specialized ->
  source_zfr_provable M specialized.
Proof.
  intros HB HP HG.
  destruct (source_zfr_separation_container_total M phi count p1 A HB HP) as (other&HOther&POther).
  pose proof (code_relation_functional M (E_separation_container(CEvar 0)(CEvar 1))
    (source_separation_container_environment M A p1) other specialized HOther HG) as E.
  now subst other.
Qed.
Print Assumptions source_zfr_separation_container_total.
Print Assumptions source_zfr_separation_container.
