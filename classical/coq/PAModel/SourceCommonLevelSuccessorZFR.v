(** Actual uniform ZFR proof of the common-level successor implication.
    The only hierarchy inputs are constructed from their proved literal laws. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
  SourceBounded SourceTraceBounds SourceBoundMonotone NumericalContexts NumericalEnvironments NumericalSourceFull
  SourceAxiomContexts SourceDescriptorProvability SourceFiniteProofContexts SourceSetTheoryDescriptors SourceZFRProvability
  SourceContextTransport SourceContextProofHelpers SourceLeastOrdinalWitness SourceProofWeakening SourceHierarchyAboveSubset SourceHierarchySubsetShell
  SourceCommonLevelRecipe SourceCommonLevelWitness SourceCommonLevelAbove SourceCommonLevelSuccessor
  SourceDomainInstances SourceLFixed NumericalInstantiation.
From Stdlib Require Import Lists.List setoid_ring.Ring.
Import ListNotations.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.

Lemma source_common_parameter_bound M i count start :coding_lt M i(succM M count) ->
  coding_lt M(addM M i start)(succM M(addM M count start)).
Proof.
  intros(r&E). apply(succ_injective M count(addM M i r)) in E. exists r.
  rewrite E. f_equal. rewrite <- !Arithmetic.add_assoc.
  rewrite(Arithmetic.add_comm M r start). reflexivity.
Qed.

Theorem source_zfr_common_successor_laws M start count :exists aboveLaw subsetLaw,
  source_common_above_laws M(succM M(succM M start))count(code_numeral M 1)(zeroM M)aboveLaw subsetLaw /\
  source_zfr_provable M aboveLaw /\source_zfr_provable M subsetLaw.
Proof.
  destruct(source_zfr_hierarchy_above_subset_shell M(addM M count(succM M(succM M start)))(code_numeral M 1))
    as(ly&og&exD&bodyD&bodyY&od&subset&pair&level&inner&member&tail&aboveLaw&HAbove&HSubset&PAbove).
  destruct(source_zfr_hierarchy_subset_shell M(code_numeral M 3)(code_numeral M 1)(code_numeral M 2)(zeroM M))
    as(od2&oe2&subset2&ld2&le2&result2&subsetLaw&HSub&PSub).
  exists aboveLaw,subsetLaw. split;[|auto]. split.
  - exists ly,og,exD,bodyD,bodyY,od,subset,pair,level,inner,member,tail. split;assumption.
  - exists od2,oe2,subset2,ld2,le2,result2. exact HSub.
Qed.

Theorem source_zfr_common_level_successor M start count old ly target tail result :
  source_common_level_recipe M start count old ->
  numerical_instantiation M(source_L_domain_code M)(addM M count start)ly ->
  source_common_level_recipe M start(succM M count)target ->
  sf_relation M SFImpl ly target tail ->sf_relation M SFImpl old tail result ->source_zfr_provable M result.
Proof.
  intros HOld HLY HTarget HTail HResult.
  destruct(source_zfr_common_successor_laws M start count) as(aboveLaw&subsetLaw&HLaws&PAbove&PSubset).
  assert(Premises:forall f,In f[aboveLaw;subsetLaw] ->source_descriptor_provable M ZFRSourceDescriptor f).
  { intros f[<-|[<-|[]]];apply(proj2(source_zfr_descriptor_provable M _));assumption. }
  destruct(source_descriptor_finite_common_context M ZFRSourceDescriptor _ Premises) as(b&c&n&HBase&P).
  pose proof(proj1 HBase) as HClosed.
  set(k:=succM M(addM M count start)).
  assert(HNames:forall i,coding_lt M i(succM M count) ->coding_lt M(addM M i start)k).
  { intros i HI. exact(source_common_parameter_bound M i count start HI). }
  assert(HNamesPrefix:forall i,coding_lt M i count ->coding_lt M(addM M i start)k).
  { intros i HI. exact(HNames i(coding_lt_trans M i count(succM M count)HI(coding_lt_succ M count))). }
  pose proof(source_common_level_recipe_bounded M start count old k HNamesPrefix HOld) as BOld.
  pose proof(source_common_level_recipe_bounded M start(succM M count)target k HNames HTarget) as BTarget.
  pose proof(source_domain_instance_bound M(source_L_domain_code M)(addM M count start)ly k
    (numerical_L_domain_bounded M)(coding_lt_succ M(addM M count start))HLY) as BLY.
  assert(BTail:source_bounded M tail k).
  { exact(proj2(source_bounded_accept_binary M SFImpl ly target tail k(or_intror(or_intror eq_refl))HTail)(conj BLY BTarget)). }
  assert(BResult:source_bounded M result k).
  { exact(proj2(source_bounded_accept_binary M SFImpl old tail result k(or_intror(or_intror eq_refl))HResult)(conj BOld BTail)). }
  pose proof(context_bounded_monotone M b c n(zeroM M)k HClosed(coding_zero_lt_succ M k)) as HC.
  destruct(environment_cons_total M b c n old) as(ob&oc&on&HConsOld).
  pose proof(proj2(context_bounded_cons M b c n old ob oc on k HConsOld)(conj BOld HC)) as HOC.
  destruct(environment_cons_total M ob oc on ly) as(lb&lc&ln&HConsLY).
  pose proof(proj2(context_bounded_cons M ob oc on ly lb lc ln k HConsLY)(conj BLY HOC)) as HLC.
  pose proof(source_full_cons_head M b c n old ob oc on k HConsOld BOld HOC) as POld.
  pose proof(source_full_cons_weaken M ob oc on ly lb lc ln k old HConsLY HLC POld) as POldL.
  pose proof(source_full_cons_head M ob oc on ly lb lc ln k HConsLY BLY HLC) as PLY.
  assert(HIncl:context_included M b c n lb lc ln).
  { intros f HF. exact(source_cons_tail_inclusion M ob oc on ly lb lc ln HConsLY f
      (source_cons_tail_inclusion M b c n old ob oc on HConsOld f HF)). }
  pose proof(source_full_common_level_successor M lb lc ln b c n k start count old ly target aboveLaw subsetLaw
    HLC HClosed HIncl HNames HOld HLY HTarget HLaws(P aboveLaw ltac:(cbn;tauto))(P subsetLaw ltac:(cbn;tauto))POldL PLY) as PTarget.
  pose proof(full_source_II M ob oc on ly target tail lb lc ln(ex_intro _ k(conj BTail HOC))PTarget HConsLY HTail) as PTail.
  apply(proj1(source_zfr_descriptor_provable M result)). exists b,c,n. split;[exact HBase|].
  exact(full_source_II M b c n old tail result ob oc on(ex_intro _ k(conj BResult HC))PTail HConsOld HResult).
Qed.
Print Assumptions source_zfr_common_successor_laws.
Print Assumptions source_zfr_common_level_successor.
