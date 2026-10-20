(** The full genuine ExA successor theorem: every auxiliary witness is eliminated. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded SourceBoundMonotone SourceClosedShift
 SourceQuantifierRules NumericalContexts NumericalSourceFull SourcePieceBoundMaxJoint
 SourceFiniteTelescope SourceFiniteTelescopeExists SourceZFRFiniteRule
 SourceRecursionPrimitiveRelations SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionStructureGraphs SourceRecursionStructureBounds
 SourceRecursionPrimitiveShifts SourceRecursionNonzeroTransport SourceRecursionAppExists SourceRecursionExistsAttempt SourceRecursionTotalRelation
 SourceRecursionExtensionInputShift SourceRecursionExAAdjoin SourceRecursionExAFromAttempt SourceRecursionAtomicShift SourceZFRProvability.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_rec_exa_successor M phi o a N z next total nonzero inj mz sz old target law k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M z k ->coding_lt M next k ->
 source_rec_total_relation M phi total ->source_rec_nonzero M o N nonzero ->source_rec_injectivity M N inj ->
 sf_relation M SFMember z N mz ->source_rec_successor M z next sz ->source_rec_exa M phi z o a N old ->source_rec_exa M phi next o a N target ->
 source_finite_telescope M[total;nonzero;inj;mz;sz;old]target law ->source_zfr_provable M law.
Proof.
 intros BP BO BA BN BZ BNext HG HNZ HI HMZ HSZ HOld HTarget HLaw. set(s:=succM M).
 set(A:=[total;nonzero;inj;mz;sz]).
 pose proof(source_rec_total_relation_closed M phi total BP HG)as BTotal0.
 assert(BTotal:source_bounded M total k)by exact(source_bounded_monotone M total(zeroM M)k BTotal0(coding_zero_lt_succ M k)).
 pose proof(source_rec_nonzero_bounded M o N nonzero k BO BN HNZ)as BNZ.
 pose proof(source_rec_injectivity_bounded M N inj k BN HI)as BInj.
 pose proof(proj2(source_bounded_accept_atom M SFMember z N mz k(or_introl eq_refl)HMZ)(conj BZ BN))as BMZ.
 pose proof(source_rec_successor_bounded M z next sz k BZ BNext HSZ)as BSZ.
 assert(Bounds:forall x,In x A ->source_bounded M x k)by(intros x[<-|[<-|[<-|[<-|[<-|[]]]]]];assumption).
 pose proof(source_rec_exa_bounded M phi next o a N target k BP BNext BO BA BN HTarget)as BTarget.
 pose proof(source_rec_exa_bounded M phi z o a N old k BP BZ BO BA BN HOld)as BOld.
 destruct HOld as(att&some&body&HAtt&HSome&HAnd&HEx).
 destruct(source_rec_nonzero_total M(s o)(s N))as(nonzeroS&HNZS).
 destruct(source_rec_injectivity_total M(s N))as(injS&HIS).
 destruct(sf_relation_total M SFMember(s z)(s N))as(mzS&HMZS).
 destruct(source_rec_successor_total M(s z)(s next))as(szS&HSZS).
 set(AS:=[total;nonzeroS;injS;mzS;szS]).
 assert(HShift:Forall2(source_formula_shift M)A AS).
 { constructor;[exact(source_closed_shift_self M total BTotal0)|].
   constructor;[exact(source_rec_nonzero_shift M o N nonzero nonzeroS HNZ HNZS)|].
   constructor;[exact(source_rec_injectivity_shift M N inj injS HI HIS)|].
   constructor;[exact(source_rec_member_shift M z N mz mzS HMZ HMZS)|].
   constructor;[exact(source_rec_successor_shift M z next sz szS HSZ HSZS)|constructor]. }
 destruct(source_rec_exa_total M phi(s next)(s o)(s a)(s N))as(targetS&HTargetS).
 pose proof(source_rec_exa_shift M phi next o a N target targetS BP HTarget HTargetS)as STarget.
 pose proof(source_rec_exa_bounded M phi(s next)(s o)(s a)(s N)targetS(s k)BP ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HTargetS)as BTargetS.
 pose proof(proj1(source_bounded_accept_unary M SFEx body old k(or_intror eq_refl)HEx)BOld)as BBody.
 destruct(source_finite_telescope_total M(AS++[body])targetS)as(deep&HDeep).
 assert(PDeep:source_zfr_provable M deep).
 { destruct(source_finite_telescope_total M[total;nonzeroS;injS;mzS;szS;att;some]targetS)as(use&HUse).
   pose proof(source_zfr_rec_exa_from_attempt M phi(s o)(s a)(s N)(zeroM M)(s z)(s next)
    total nonzeroS injS att mzS szS some targetS use(s k)BP ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)
    ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)ltac:(rec_exa_name_bound)HG HNZS HIS HAtt HMZS HSZS HSome HTargetS HUse)as PUse.
   apply(source_zfr_finite_rule M[use](AS++[body])targetS deep(s k));[|exact BTargetS|exact HDeep| |].
   - intros x HX. apply in_app_or in HX. destruct HX as[HX|[<-|[]]];[exact(source_finite_shifted_bounds M A AS k HShift Bounds x HX)|exact BBody].
   - intros x[<-|[]]. exact PUse.
   - intros cb cc cn BC Laws Premises.
     assert(PBody:source_full_prv M cb cc cn body)by(apply Premises,in_or_app;right;now left).
     destruct(source_full_piece_conjunction_components M cb cc cn att some body HAnd PBody)as[PT PS].
     apply(source_full_finite_telescope_apply M[total;nonzeroS;injS;mzS;szS;att;some]targetS use HUse cb cc cn).
     + apply Laws. now left.
     + intros x[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]];first[exact PT|exact PS|apply Premises,in_or_app;left;unfold AS;cbn;tauto]. }
 exact(source_zfr_finite_telescope_exists M A AS body old target targetS deep law k Bounds BOld BTarget HShift HEx STarget HDeep HLaw PDeep).
Qed.
Print Assumptions source_zfr_rec_exa_successor.
