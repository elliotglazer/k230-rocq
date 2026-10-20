(** The actual ExA subset contains the starting index. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull
 SourceFiniteTelescope SourceZFRFiniteRule SourceDerivedRules SourceRecursionPrimitiveRelations SourceRecursionStructureGraphs SourceRecursionStructureBounds
 SourceRecursionExistsAttempt SourceRecursionExABase SourceRecursionExASubset SourceRecursionExASubsetTransport SourceRecursionExASubsetRules SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_exa_subset_zero M phi o a N X nonzero chart mn mx law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M X k ->
 source_rec_nonzero M o N nonzero ->source_rec_exa_subset_chart M phi o a N X chart ->
 sf_relation M SFMember o N mn ->sf_relation M SFMember o X mx ->source_finite_telescope M[nonzero;chart;mn]mx law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BX HNZ HChart HMN HMX HLaw.
 destruct(source_rec_exa_total M phi o o a N)as(exa&HExA).
 destruct(sf_relation_total M SFImpl nonzero exa)as(base&HBase).
 pose proof(source_zfr_rec_exa_base M phi o a N nonzero exa base k BP BO BA BN HNZ HExA HBase)as PBase.
 pose proof(source_rec_nonzero_bounded M o N nonzero k BO BN HNZ)as BNZ.
 pose proof(source_rec_exa_subset_chart_bounded M phi o a N X chart k BP BO BA BN BX HChart)as BChart.
 pose proof(proj2(source_bounded_accept_atom M SFMember o N mn k(or_introl eq_refl)HMN)(conj BO BN))as BMN.
 pose proof(proj2(source_bounded_accept_atom M SFMember o X mx k(or_introl eq_refl)HMX)(conj BO BX))as BMX.
 apply(source_zfr_finite_rule M[base][nonzero;chart;mn]mx law k).
 - intros x[<-|[<-|[<-|[]]]];assumption.
 - exact BMX.
 - exact HLaw.
 - intros x[<-|[]]. exact PBase.
 - intros cb cc cn BC Laws Premises.
   pose proof(source_full_modus_ponens M cb cc cn nonzero exa base HBase(Laws base(or_introl eq_refl))(Premises nonzero(or_introl eq_refl)))as PExA.
   exact(source_full_rec_exa_subset_chart_in M cb cc cn phi o a N X o chart mx mn exa BP HChart HMX HMN HExA
    (Premises chart ltac:(cbn;tauto))(Premises mn ltac:(cbn;tauto))PExA).
Qed.
Print Assumptions source_zfr_rec_exa_subset_zero.
