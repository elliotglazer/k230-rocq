(** Eliminate the old value witness in a genuine attempt. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone SourceClosedShift
 SourceQuantifierRules SourceFiniteTelescope SourceFiniteTelescopeExists SourceFiniteTelescopePermutation
 SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionAttemptTransport
 SourceRecursionStructureGraphs SourceRecursionStructureBounds SourceRecursionPrimitiveShifts SourceRecursionNonzeroTransport
 SourceRecursionAppExists SourceRecursionExistsAttempt SourceRecursionTotalRelation SourceRecursionExATotalValue SourceRecursionExAAdjoin
 SourceRecursionExtensionInputShift SourceRecursionShiftGraphs SourceRecursionAtomicShift SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_exa_from_attempt M phi o a N f z next total nonzero inj att mz sz some target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->coding_lt M z k ->coding_lt M next k ->
 source_rec_total_relation M phi total ->source_rec_nonzero M o N nonzero ->source_rec_injectivity M N inj ->source_rec_attempt M phi o a N f att ->
 sf_relation M SFMember z N mz ->source_rec_successor M z next sz ->source_rec_app_exists M f z some ->source_rec_exa M phi next o a N target ->
 source_finite_telescope M[total;nonzero;inj;mz;sz;att;some]target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BF BZ BNext HG HNZ HI HT HMZ HSZ HSome HTarget HLaw. set(s:=succM M).
 set(A:=[total;nonzero;inj;mz;sz;att]).
 pose proof(source_rec_total_relation_closed M phi total BP HG)as BTotal0.
 assert(BTotal:source_bounded M total k)by exact(source_bounded_monotone M total(zeroM M)k BTotal0(coding_zero_lt_succ M k)).
 pose proof(source_rec_nonzero_bounded M o N nonzero k BO BN HNZ)as BNZ.
 pose proof(source_rec_injectivity_bounded M N inj k BN HI)as BInj.
 pose proof(source_rec_attempt_bounded M phi o a N f att k BP BO BA BN BF HT)as BAtt.
 pose proof(proj2(source_bounded_accept_atom M SFMember z N mz k(or_introl eq_refl)HMZ)(conj BZ BN))as BMZ.
 pose proof(source_rec_successor_bounded M z next sz k BZ BNext HSZ)as BSZ.
 assert(Bounds:forall x,In x A ->source_bounded M x k)by(intros x[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];assumption).
 pose proof(source_rec_exa_bounded M phi next o a N target k BP BNext BO BA BN HTarget)as BTarget.
 pose proof(source_rec_app_exists_bounded M f z some k BF BZ HSome)as BSome.
 destruct HSome as(body&HBody&HEx).
 destruct(source_rec_nonzero_total M(s o)(s N))as(nonzeroS&HNZS).
 destruct(source_rec_injectivity_total M(s N))as(injS&HIS).
 destruct(source_rec_attempt_total M phi(s o)(s a)(s N)(s f))as(attS&HTS).
 destruct(sf_relation_total M SFMember(s z)(s N))as(mzS&HMZS).
 destruct(source_rec_successor_total M(s z)(s next))as(szS&HSZS).
 set(AS:=[total;nonzeroS;injS;mzS;szS;attS]).
 assert(HShift:Forall2(source_formula_shift M)A AS).
 { constructor;[exact(source_closed_shift_self M total BTotal0)|].
   constructor;[exact(source_rec_nonzero_shift M o N nonzero nonzeroS HNZ HNZS)|].
   constructor;[exact(source_rec_injectivity_shift M N inj injS HI HIS)|].
   constructor;[exact(source_rec_member_shift M z N mz mzS HMZ HMZS)|].
   constructor;[exact(source_rec_successor_shift M z next sz szS HSZ HSZS)|].
   constructor;[exact(source_rec_attempt_shift M phi o a N f att attS BP HT HTS)|constructor]. }
 destruct(source_rec_exa_total M phi(s next)(s o)(s a)(s N))as(targetS&HTargetS).
 pose proof(source_rec_exa_shift M phi next o a N target targetS BP HTarget HTargetS)as STarget.
 pose proof(source_rec_exa_bounded M phi(s next)(s o)(s a)(s N)targetS(s k)BP ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HTargetS)as BTargetS.
 destruct(source_finite_telescope_total M(AS++[body])targetS)as(deep&HDeep).
 assert(PDeep:source_zfr_provable M deep).
 { destruct(source_finite_telescope_total M[total;nonzeroS;injS;attS;mzS;szS;body]targetS)as(natural&HNatural).
   pose proof(source_zfr_rec_exa_from_attempt_value M phi(s o)(s a)(s N)(s f)(s z)(s next)(zeroM M)
    total nonzeroS injS attS mzS szS body targetS natural(s k)BP ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)
    ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HG HNZS HIS HTS HMZS HSZS HBody HTargetS HNatural)as PNatural.
   apply(source_zfr_finite_telescope_inclusion M[total;nonzeroS;injS;attS;mzS;szS;body](AS++[body])targetS natural deep(s k));[|exact BTargetS|exact HNatural|exact HDeep| |exact PNatural].
   - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]].
     + exact(source_finite_shifted_bounds M A AS k HShift Bounds x HX).
     + exact(source_rec_app_bounded M(s f)(s z)(zeroM M)body(s k)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HBody).
   - intros x HX. unfold AS. cbn in HX|-*. tauto. }
 exact(source_zfr_finite_telescope_exists M A AS body some target targetS deep law k Bounds BSome BTarget HShift HEx STarget HDeep HLaw PDeep).
Qed.
Print Assumptions source_zfr_rec_exa_from_attempt.
