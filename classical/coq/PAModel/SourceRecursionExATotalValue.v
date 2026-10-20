(** Use genuine totality of the internal relation to supply the next value. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone SourceQuantifierRules
 NumericalContexts NumericalSourceFull SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionAttemptTransport
 SourceRecursionStructureGraphs SourceRecursionStructureBounds SourceRecursionPrimitiveShifts SourceRecursionNonzeroTransport
 SourceRecursionExAStepInputs SourceRecursionExAAdjoin SourceRecursionExAPair SourceRecursionExistsAttempt SourceRecursionTotalRelation
 SourceRecursionExtensionInputShift SourceRecursionAtomicShift SourceRecursionShiftGraphs SourceRecursionBinaryInstance SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_exa_from_attempt_value M phi o a N f z next p total nonzero inj att mz sz appf target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M z k ->coding_lt M next k ->coding_lt M p k ->
 source_rec_total_relation M phi total ->source_rec_nonzero M o N nonzero ->source_rec_injectivity M N inj ->source_rec_attempt M phi o a N f att ->
 sf_relation M SFMember z N mz ->source_rec_successor M z next sz ->source_rec_app M f z p appf ->source_rec_exa M phi next o a N target ->
 source_finite_telescope M[total;nonzero;inj;att;mz;sz;appf]target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BZ BNext BP' HG HNZ HI HT HMZ HSZ HAF HTarget HLaw. set(s:=succM M).
 set(A:=[nonzero;inj;att;mz;sz;appf]).
 assert(Bounds:forall x,In x A ->source_bounded M x k).
 { intros x[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
   - exact(source_rec_nonzero_bounded M o N nonzero k BO BN HNZ).
   - exact(source_rec_injectivity_bounded M N inj k BN HI).
   - exact(source_rec_attempt_bounded M phi o a N f att k BP BO BA BN BF HT).
   - exact(proj2(source_bounded_accept_atom M SFMember z N mz k(or_introl eq_refl)HMZ)(conj BZ BN)).
   - exact(source_rec_successor_bounded M z next sz k BZ BNext HSZ).
   - exact(source_rec_app_bounded M f z p appf k BF BZ BP' HAF). }
 pose proof(source_rec_exa_bounded M phi next o a N target k BP BNext BO BA BN HTarget)as BTarget.
 destruct(source_rec_relation_witness_total M phi p)as(some&HSome).
 pose proof(source_rec_relation_witness_bounded M phi p some k BP BP' HSome)as BSome.
 destruct HSome as(body&HBody&HEx).
 assert(HSome:source_rec_relation_witness M phi p some)by(exists body;auto).
 destruct(source_rec_exa_step_inputs_total M phi(s o)(s a)(s N)(s f)(s z)(s next)(s p)(zeroM M))
  as(AS&(nonzeroS&injS&attS&mzS&szS&appfS&binaryS&E&HNZS&HIS&HTS&HMZS&HSZS&HAFS&HGS)).
 pose proof(source_rec_binary_functional M phi(s p)(zeroM M)binaryS body HGS HBody)as EBody. subst binaryS.
 set(B:=[nonzeroS;injS;attS;mzS;szS;appfS]).
 assert(HShift:Forall2(source_formula_shift M)A B).
 { constructor;[exact(source_rec_nonzero_shift M o N nonzero nonzeroS HNZ HNZS)|].
   constructor;[exact(source_rec_injectivity_shift M N inj injS HI HIS)|].
   constructor;[exact(source_rec_attempt_shift M phi o a N f att attS BP HT HTS)|].
   constructor;[exact(source_rec_member_shift M z N mz mzS HMZ HMZS)|].
   constructor;[exact(source_rec_successor_shift M z next sz szS HSZ HSZS)|].
   constructor;[exact(source_rec_app_shift M f z p appf appfS HAF HAFS)|constructor]. }
 destruct(source_rec_exa_total M phi(s next)(s o)(s a)(s N))as(targetS&HTargetS).
 pose proof(source_rec_exa_shift M phi next o a N target targetS BP HTarget HTargetS)as STarget.
 destruct(source_finite_telescope_total M(B++[body])targetS)as(deep&HDeep).
 assert(PDeep:source_zfr_provable M deep).
 { assert(HInputs:source_rec_exa_step_inputs M phi(s o)(s a)(s N)(s f)(s z)(s next)(s p)(zeroM M)(B++[body])).
   { exists nonzeroS,injS,attS,mzS,szS,appfS,body. split;[reflexivity|]. auto 10. }
   apply(source_zfr_rec_exa_from_step_values M phi(s o)(s a)(s N)(s f)(s z)(s next)(s p)(zeroM M)(B++[body])targetS deep(s k));try rec_exa_name_bound;assumption. }
 destruct(source_finite_telescope_total M(A++[some])target)as(withSome&HWithSome).
 pose proof(source_zfr_finite_telescope_exists M A B body some target targetS deep withSome k Bounds BSome BTarget HShift HEx STarget HDeep HWithSome PDeep)as PWithSome.
 apply(source_zfr_finite_rule M[withSome][total;nonzero;inj;att;mz;sz;appf]target law k).
 - intros x[<-|HX];[|exact(Bounds x HX)].
   apply(source_bounded_monotone M total(zeroM M)k(source_rec_total_relation_closed M phi total BP HG)). exact(coding_zero_lt_succ M k).
 - exact BTarget.
 - exact HLaw.
 - intros x[<-|[]]. exact PWithSome.
 - intros cb cc cn BC Laws Premises.
   assert(PSome:source_full_prv M cb cc cn some).
   { exact(source_full_rec_total_relation_use M cb cc cn phi total p some BP HG HSome(Premises total(or_introl eq_refl))). }
   apply(source_full_finite_telescope_apply M(A++[some])target withSome HWithSome cb cc cn).
   + apply Laws. now left.
   + intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[apply Premises;now right|exact PSome].
Qed.
Print Assumptions source_zfr_rec_exa_from_attempt_value.
