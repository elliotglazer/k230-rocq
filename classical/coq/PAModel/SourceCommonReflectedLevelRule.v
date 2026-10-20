(** Actual ZFR implication for the shared reflected-level point. Its only
    antecedents are the old common point, the ordinary reflection point,
    and the new hierarchy instance. The fixed LL proof is constructed. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 SourceCommonReflectedLevel SourceCommonLevelPoint SourceOrdinaryReflectionExists SourceOrdinaryReflectionSyntax
 SourceHierarchyStrictShell SourceHierarchySyntax SourceOrdinalPredicate NumericalInstantiation SourcePHHierarchyOrdinals
 SourceMembershipBlocks SourceMembershipBlockMonotone SourceRawSubset SourceConjunctionRules SourceUpperProofHelpers
 NumericalSourceFull SourceFiniteTelescope SourceZFRFiniteRule SourceZFRProvability SourceLFixed.
From Stdlib Require Import Lists.List.
Import ListNotations.
Unset Implicit Arguments.
Theorem source_zfr_common_reflected_level_core M start paramCount reflectCount phi seed oldY beta Y
 common reflection level target law k:
 source_bounded M phi reflectCount ->
 (forall i,coding_lt M i paramCount ->coding_lt M(addM M i start)k) ->
 coding_lt M seed k ->coding_lt M oldY k ->coding_lt M beta k ->coding_lt M Y k ->
 source_common_level_point M start paramCount seed oldY common ->
 source_ordinary_reflection_point M(source_L_domain_code M)reflectCount phi seed beta reflection ->
 source_LL_instance M beta Y level ->source_common_reflected_level_point M start paramCount reflectCount phi beta Y target ->
 source_finite_telescope M[common;reflection;level]target law ->source_zfr_provable M law.
Proof.
 intros BF HNames BSeed BOldY BBeta BY HCommon HReflection HLevel HTarget HLaw.
 pose proof(source_common_level_point_bounded M start paramCount seed oldY common k HNames BSeed BOldY HCommon)as BCommon.
 pose proof(source_ordinary_reflection_point_bounded M(source_L_domain_code M)reflectCount phi seed beta reflection k
  (numerical_L_domain_bounded M)BF BSeed BBeta HReflection)as BReflection.
 pose proof(source_LL_instance_bounded M beta Y level k BBeta BY HLevel)as BLevel.
 pose proof(source_common_reflected_level_point_bounded M start paramCount reflectCount phi beta Y target k BF HNames BBeta BY HTarget)as BTarget.
 destruct HCommon as(oldMembers&oldOrdinal&oldLevel&oldPair&HM&HO&HL&HPair&HCommon).
 destruct HReflection as(ordinal&limit&member&refl&tail&middle&HOrdinal&HLimit&HMember&HRefl&HTail&HMiddle&HReflection).
 destruct HTarget as(newCommon&newRefl&HNewCommon&HNewRefl&HTarget).
 destruct HNewCommon as(newMembers&newOrdinal&newLevel&newPair&HNM&HNO&HNL&HNP&HNewCommon).
 pose proof(numerical_instantiation_functional M _ beta ordinal newOrdinal HOrdinal HNO)as E;subst newOrdinal.
 pose proof(source_LL_instance_functional M beta Y level newLevel HLevel HNL)as E;subst newLevel.
 pose proof(source_ordinary_reflection_functional M _ reflectCount phi beta refl newRefl HRefl HNewRefl)as E;subst newRefl.
 destruct(source_zfr_hierarchy_strict_shell M seed beta oldY Y)
  as(od&oe&mem&ld&le&inLevel&subset&pair&strict&HO'&HOrdinal'&HMember'&HL'&HLevel'&HInLevel&HSubset&HAnd&HStrict&PStrict).
 pose proof(numerical_instantiation_functional M _ seed oldOrdinal od HO HO')as E;subst od.
 pose proof(numerical_instantiation_functional M _ beta ordinal oe HOrdinal HOrdinal')as E;subst oe.
 pose proof(sf_relation_functional M SFMember seed beta member mem HMember HMember')as E;subst mem.
 pose proof(source_LL_instance_functional M seed oldY oldLevel ld HL HL')as E;subst ld.
 pose proof(source_LL_instance_functional M beta Y level le HLevel HLevel')as E;subst le.
 apply(source_zfr_finite_rule M[strict][common;reflection;level]target law k).
 - intros a[<-|[<-|[<-|[]]]];assumption.
 - exact BTarget.
 - exact HLaw.
 - intros f[<-|[]]. exact PStrict.
 - intros b c n BC Laws Premises.
   assert(PCommon:source_full_prv M b c n common)by(apply Premises;now left).
   assert(PReflection:source_full_prv M b c n reflection)by(apply Premises;right;now left).
   assert(PLevel:source_full_prv M b c n level)by(apply Premises;right;right;now left).
   pose proof(source_full_conjunction_left M b c n oldPair oldMembers common HCommon PCommon)as POldPair.
   pose proof(source_full_conjunction_left M b c n oldOrdinal oldLevel oldPair HPair POldPair)as POldOrdinal.
   pose proof(source_full_conjunction_right M b c n oldOrdinal oldLevel oldPair HPair POldPair)as POldLevel.
   pose proof(source_full_conjunction_right M b c n oldPair oldMembers common HCommon PCommon)as POldMembers.
   pose proof(source_full_conjunction_left M b c n ordinal middle reflection HReflection PReflection)as POrdinal.
   pose proof(source_full_conjunction_right M b c n ordinal middle reflection HReflection PReflection)as PMiddle.
   pose proof(source_full_conjunction_right M b c n limit tail middle HMiddle PMiddle)as PTail.
   pose proof(source_full_conjunction_left M b c n member refl tail HTail PTail)as PMember.
   pose proof(source_full_conjunction_right M b c n member refl tail HTail PTail)as PRefl.
   assert(PPair:source_full_prv M b c n pair).
   { apply(source_full_finite_telescope_apply M[oldOrdinal;ordinal;member;oldLevel;level]pair strict HStrict b c n(Laws strict(or_introl eq_refl))).
     intros f[<-|[<-|[<-|[<-|[<-|[]]]]]];assumption. }
   pose proof(source_full_conjunction_right M b c n inLevel subset pair HAnd PPair)as PSubset.
   pose proof(source_full_membership_block_monotone M start oldY Y paramCount oldMembers newMembers subset b c n k
    HNames BOldY BY HM HNM HSubset BC POldMembers PSubset)as PNewMembers.
   pose proof(source_full_conjunction M b c n ordinal level newPair HNP POrdinal PLevel)as PNewPair.
   pose proof(source_full_conjunction M b c n newPair newMembers newCommon HNewCommon PNewPair PNewMembers)as PNewCommon.
   exact(source_full_conjunction M b c n newCommon refl target HTarget PNewCommon PRefl).
Qed.
Print Assumptions source_zfr_common_reflected_level_core.
