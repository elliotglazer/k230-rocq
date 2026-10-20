(** Actual ordinary ZFR proof of the cofinal successor telescope. The
    only finite geometry theorem is constructed from the pinned proof. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceBoundMonotone SourceTraceBounds NumericalContexts NumericalSourceFull SourceContextTransport SourceFiniteFamilyBounds
 SourceAxiomContexts SourceDescriptorProvability SourceFiniteProofContexts SourceSetTheoryDescriptors SourceZFRProvability
 SourceFiniteTelescope SourceCofinalGeometry SourceCofinalCommonRecipe SourceCofinalCommonWitness
 SourceCommonLevelSuccessorZFR SourceCofinalSuccessorLaws SourceCofinalCommonSuccessor.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Lemma source_cofinal_name_bound M start count Ks Lb:exists k,
 coding_lt M Ks k /\coding_lt M Lb k /\coding_lt M(addM M count start)k /\
 (forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i start)k).
Proof.
 destruct(source_finite_names_bound M[addM M count start;Ks;Lb])as(k&H).
 assert(HMax:coding_lt M(addM M count start)k)by(apply H;cbn;tauto).
 exists k. repeat split;try(apply H;cbn;tauto);try exact HMax.
 intros i HI. exact(source_bound_lt_le M(addM M i start)(succM M(addM M count start))k
 (source_common_parameter_bound M i count start HI)
 (proj2(coding_lt_succ_cancel M(addM M count start)k)HMax)).
Qed.
Theorem source_zfr_cofinal_common_successor M start count Ks Lb old newmember target ordinals cover result:
 source_cofinal_common_recipe M start count Ks old ->sf_relation M SFMember(addM M count start)Lb newmember ->
 source_cofinal_common_recipe M start(succM M count)Ks target ->
 source_cofinal_ordinals M Ks ordinals ->source_cofinal_cover M Ks Lb cover ->
 source_finite_telescope M[ordinals;cover;old;newmember]target result ->source_zfr_provable M result.
Proof.
 intros HOld HNew HTarget HOrd HCover HResult.
 destruct(source_zfr_cofinal_successor_law M start count Ks Lb)as(law&HLaw&PLaw).
 assert(Premises:forall f,In f[law] ->source_descriptor_provable M ZFRSourceDescriptor f).
 { intros f[<-|[]]. exact(proj2(source_zfr_descriptor_provable M law)PLaw). }
 destruct(source_descriptor_finite_common_context M ZFRSourceDescriptor _ Premises)as(b&c&n&HBase&P).
 pose proof(proj1 HBase)as HClosed.
 destruct(source_cofinal_name_bound M start count Ks Lb)as(k&HKs&HLb&HLast&HNames).
 assert(HNamesPrefix:forall i,coding_lt M i count ->coding_lt M(addM M i start)k).
 { intros i HI. exact(HNames i(coding_lt_trans M i count(succM M count)HI(coding_lt_succ M count))). }
 pose proof(source_cofinal_common_recipe_bounded M start count Ks old k HNamesPrefix HKs HOld)as BOld.
 pose proof(source_cofinal_common_recipe_bounded M start(succM M count)Ks target k HNames HKs HTarget)as BTarget.
 pose proof(source_cofinal_ordinals_bounded M Ks ordinals k HKs HOrd)as BOrd.
 pose proof(source_cofinal_cover_bounded M Ks Lb cover k HKs HLb HCover)as BCover.
 pose proof(proj2(source_bounded_accept_atom M SFMember(addM M count start)Lb newmember k(or_introl eq_refl)HNew)(conj HLast HLb))as BNew.
 pose proof(context_bounded_monotone M b c n(zeroM M)k HClosed(coding_zero_lt_succ M k))as HC.
 apply(proj1(source_zfr_descriptor_provable M result)). exists b,c,n. split;[exact HBase|].
 apply(source_full_finite_telescope M[ordinals;cover;old;newmember]target result k).
 - intros f[<-|[<-|[<-|[<-|[]]]]];assumption.
 - exact BTarget.
 - exact HResult.
 - exact HC.
 - intros db dc dn HDC HIncl Proved.
   exact(source_full_cofinal_common_successor M db dc dn b c n k start count Ks Lb old newmember target ordinals cover law
   HDC HClosed HIncl HNames HKs HOld HNew HTarget HOrd HCover HLaw(P law ltac:(cbn;tauto))
   (Proved ordinals ltac:(cbn;tauto))(Proved cover ltac:(cbn;tauto))(Proved old ltac:(cbn;tauto))(Proved newmember ltac:(cbn;tauto))).
Qed.
Print Assumptions source_cofinal_name_bound.
Print Assumptions source_zfr_cofinal_common_successor.
