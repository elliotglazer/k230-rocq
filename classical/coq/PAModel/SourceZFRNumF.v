(** Actual ZFR witnesses for every internal NumF numeral. This is PA
    induction on model-valued indices, not lifting an external family of proofs. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SourceDefinabilityPrimitives
 SourceDefinabilitySuccessor SourceDefinabilityBounds SourceNumFProofInduction
 SourceClosureNumeralsOld SourceClosureNumeralsFixed OldNamedSyntaxBridge OldFullNDSourceBridge
 SourceDescriptorProvability SourceSetTheoryDescriptors SourceZFRProvability.
Unset Implicit Arguments.
Lemma definability_empty_exists_exact :source_def_empty_exists=source_empty_exists_law.
Proof. reflexivity. Qed.
Lemma definability_successor_exists_exact :source_def_succ_exists=source_successor_exists_law.
Proof.
 unfold source_def_succ_exists,source_def_succ10,source_def_successor01,
  source_successor_exists_law,old_successor_exists_law.
 reflexivity.
Qed.
Theorem source_zfr_numf_exists M n matrix ex :source_numf M n matrix ->
 sf_relation M SFEx matrix(zeroM M) ex ->source_zfr_provable M ex.
Proof.
 intros HM HE. apply(proj1(source_zfr_descriptor_provable M ex)).
 refine(source_descriptor_numf_induction M ZFRSourceDescriptor _ _ n matrix ex HM HE).
 - rewrite definability_empty_exists_exact. apply(proj2(source_zfr_descriptor_provable M _)).
   apply source_zfr_empty_exists.
 - rewrite definability_successor_exists_exact. apply(proj2(source_zfr_descriptor_provable M _)).
   apply source_zfr_successor_exists_numeral.
Qed.
Theorem source_zfr_numf_exists_total M n :exists matrix ex,source_numf M n matrix /\
 sf_relation M SFEx matrix(zeroM M) ex /\source_zfr_provable M ex.
Proof.
 destruct(source_numf_total M n)as(matrix&HM).
 destruct(sf_relation_total M SFEx matrix(zeroM M))as(ex&HE).
 exists matrix,ex. split;[exact HM|]. split;[exact HE|]. exact(source_zfr_numf_exists M n matrix ex HM HE).
Qed.
Print Assumptions definability_successor_exists_exact.
Print Assumptions source_zfr_numf_exists.
Print Assumptions source_zfr_numf_exists_total.
