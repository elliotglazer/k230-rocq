(** The actual witness branch proving successor closure of an agreement subset. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone
 NumericalContexts NumericalSourceFull SourceTraceBounds SourceInstantiationConstructors SourceQuantifierRules SourcePieceBoundMaxJoint SourceDerivedRules
 SourceFiniteTelescope SourceZFRFiniteRule SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds
 SourceRecursionFunctionality SourceRecursionFunctionalityClosed SourceRecursionAgreement SourceRecursionAgreementSubset
 SourceRecursionSubsetRules SourceRecursionSuccessorIn SourceRecursionInductionTransport SourceRecursionAgreementSuccessor
 SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_subset_successor_branch M phi o a N f g X z v funlaw af ag chart mx successor mn pair target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M g k ->
 coding_lt M X k ->coding_lt M z k ->coding_lt M v k ->source_rec_functionality M phi funlaw ->
 source_rec_attempt M phi o a N f af ->source_rec_attempt M phi o a N g ag ->source_rec_subset_chart M f g N X chart ->
 sf_relation M SFMember z X mx ->source_rec_successor M z v successor ->sf_relation M SFMember v N mn ->sf_relation M SFAnd successor mn pair ->
 source_rec_successor_in M z X target ->source_finite_telescope M[funlaw;af;ag;chart;mx;pair]target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BG BX BZ BV HFun HAF HAG HChart HMX HS HMN HPair HTarget HLaw.
 destruct(sf_relation_total M SFMember z N)as(oldMember&HOldMember).
 destruct(source_rec_agreement_total M f g z)as(oldAgr&HOldAgr).
 destruct(source_rec_agreement_total M f g v)as(newAgr&HNewAgr).
 destruct(sf_relation_total M SFMember v X)as(newMember&HNewMember).
 destruct(source_finite_telescope_total M[funlaw;af;ag;oldMember;successor;oldAgr]newAgr)as(succLaw&HSuccLaw).
 pose proof(source_zfr_rec_agreement_successor M phi o a N f g z v funlaw af ag oldMember successor oldAgr newAgr succLaw k
  BP BO BA BN BF BG BZ BV HFun HAF HAG HOldMember HS HOldAgr HNewAgr HSuccLaw)as PSuccLaw.
 assert(BFun:source_bounded M funlaw k)by exact(source_bounded_monotone M funlaw(zeroM M)k(source_rec_functionality_closed M phi funlaw BP HFun)(coding_zero_lt_succ M k)).
 assert(BAF:source_bounded M af k)by exact(source_rec_attempt_bounded M phi o a N f af k BP BO BA BN BF HAF).
 assert(BAG:source_bounded M ag k)by exact(source_rec_attempt_bounded M phi o a N g ag k BP BO BA BN BG HAG).
 assert(BChart:source_bounded M chart k).
 { destruct HChart as(point&HP&HA). apply(proj2(source_bounded_accept_unary M SFAll point chart k(or_introl eq_refl)HA)).
   exact(source_rec_subset_point_bounded M(succM M f)(succM M g)(succM M N)(succM M X)(zeroM M)point(succM M k)
    (proj2(coding_lt_succ_cancel M f k)BF)(proj2(coding_lt_succ_cancel M g k)BG)(proj2(coding_lt_succ_cancel M N k)BN)
    (proj2(coding_lt_succ_cancel M X k)BX)(coding_zero_lt_succ M k)HP). }
 assert(BMX:source_bounded M mx k)by exact(proj2(source_bounded_accept_atom M SFMember z X mx k(or_introl eq_refl)HMX)(conj BZ BX)).
 assert(BS:source_bounded M successor k)by exact(source_rec_successor_bounded M z v successor k BZ BV HS).
 assert(BMN:source_bounded M mn k)by exact(proj2(source_bounded_accept_atom M SFMember v N mn k(or_introl eq_refl)HMN)(conj BV BN)).
 assert(BPair:source_bounded M pair k)by exact(proj2(source_bounded_accept_binary M SFAnd successor mn pair k(or_introl eq_refl)HPair)(conj BS BMN)).
 pose proof(source_rec_successor_in_bounded M z X target k BZ BX HTarget)as BTarget.
 apply(source_zfr_finite_rule M[succLaw][funlaw;af;ag;chart;mx;pair]target law k).
 - intros x[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];assumption.
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[]]. exact PSuccLaw.
 - intros cb cc cn BC Laws Premises.
   assert(PFun:source_full_prv M cb cc cn funlaw)by(apply Premises;cbn;tauto).
   assert(PAF:source_full_prv M cb cc cn af)by(apply Premises;cbn;tauto).
   assert(PAG:source_full_prv M cb cc cn ag)by(apply Premises;cbn;tauto).
   assert(PChart:source_full_prv M cb cc cn chart)by(apply Premises;cbn;tauto).
   assert(PMX:source_full_prv M cb cc cn mx)by(apply Premises;cbn;tauto).
   assert(PPair:source_full_prv M cb cc cn pair)by(apply Premises;cbn;tauto).
   destruct(source_full_piece_conjunction_components M cb cc cn successor mn pair HPair PPair)as[PS PMN].
   destruct(source_full_rec_subset_chart_out M cb cc cn f g N X z chart mx oldMember oldAgr HChart HMX HOldMember HOldAgr PChart PMX)as[POldMember POldAgr].
   assert(PNewAgr:source_full_prv M cb cc cn newAgr).
   { apply(source_full_finite_telescope_apply M[funlaw;af;ag;oldMember;successor;oldAgr]newAgr succLaw HSuccLaw cb cc cn).
     - apply Laws. now left.
     - intros x[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];assumption. }
   pose proof(source_full_rec_subset_chart_in M cb cc cn f g N X v chart newMember mn newAgr HChart HNewMember HMN HNewAgr PChart PMN PNewAgr)as PNewMember.
   destruct HTarget as(targetS&targetM&targetBody&HTS&HTM&HTB&HTE).
   destruct(sf_relation_total M SFAnd successor newMember)as(instance&HInstance).
   pose proof(source_rec_successor_body_instantiation M z X targetS targetM targetBody v successor newMember instance HTS HTM HTB HS HNewMember HInstance)as HInst.
   assert(PInstance:source_full_prv M cb cc cn instance).
   { exact(full_source_CI M cb cc cn successor newMember instance(source_wf_binary M cb cc cn SFAnd successor newMember instance(or_introl eq_refl)HInstance
      (source_full_prv_wellformed M cb cc cn successor PS)(source_full_prv_wellformed M cb cc cn newMember PNewMember))PS PNewMember HInstance). }
   exact(full_source_ExI M cb cc cn targetBody target v instance(ex_intro _ k(conj BTarget BC))PInstance HTE HInst).
Qed.
Print Assumptions source_zfr_rec_subset_successor_branch.
