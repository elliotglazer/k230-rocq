(** A genuine Separation proof specialized to variable zero, uniformly
    for arbitrary internal matrices and parameter-closure lengths. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded SourceFiniteCutoffShift SourceSetTheoryDescriptors SourceZFRProvability
  SourceZFRSeparationUse SourceDescriptorInstantiation SourceSeparationZeroSpecialization.
Unset Implicit Arguments.

Theorem source_zfr_separation_zero_total M phi count p1 :
  source_bounded M phi (succM M count) -> source_cutoff_shift M 1 phi p1 ->
  exists specialized,
    code_relation M (fun _=>p1) (E_separation_zero (CEvar 0)) specialized /\
    source_zfr_provable M specialized.
Proof.
  intros HB HP.
  destruct (source_zfr_separation_open_total M phi count HB) as (body&raw&HBody&HRaw&PRaw).
  destruct (source_separation_zero_specialization M phi body raw p1 (succM M count)
    HB HBody HRaw HP) as (rawbody&specialized&HAll&HInst&HGraph).
  exists specialized. split;[exact HGraph|].
  apply (proj1 (source_zfr_descriptor_provable M specialized)).
  apply (source_descriptor_provable_all_elim M ZFRSourceDescriptor rawbody raw
    (zeroM M) specialized);[|exact HAll|exact HInst].
  exact (proj2 (source_zfr_descriptor_provable M raw) PRaw).
Qed.

Theorem source_zfr_separation_zero M phi count p1 specialized :
  source_bounded M phi (succM M count) -> source_cutoff_shift M 1 phi p1 ->
  code_relation M (fun _=>p1) (E_separation_zero (CEvar 0)) specialized ->
  source_zfr_provable M specialized.
Proof.
  intros HB HP HG.
  destruct (source_zfr_separation_zero_total M phi count p1 HB HP) as (other&HOther&POther).
  pose proof (code_relation_functional M (E_separation_zero (CEvar 0))
    (fun _=>p1) other specialized HOther HG) as E.
  now subst other.
Qed.
Print Assumptions source_zfr_separation_zero_total.
Print Assumptions source_zfr_separation_zero.
