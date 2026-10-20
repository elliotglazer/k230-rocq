(** Genuine PA count induction producing source proofs after every guarded
    parameter quantifier has been eliminated. Counts and assignments may be
    nonstandard. The only local proof inputs are the Dn instance and members. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
 NumericalEnvironments NumericalSubstitutionMaps NumericalSubstitution NumericalSourceFull SetFormulaCodes SourceBounded
 SourceRoleReopening SourceNumeralLift SourceBoundedMapComposition SourceDnStep SourceDn SourceDnIterationCommute
 SourceDnEnvironmentTail SourceDnAssignments SourceDnFirstElimination SourceDnEliminationInvariant.
From FOL Require Import FullSyntax Arithmetics.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature |0.
#[local] Existing Instance PA_preds_signature |0.
Theorem source_full_dn_elimination M:forall count,source_dn_elimination_at M count.
Proof.
 apply(definable_induction M(source_dn_elimination_at M)(source_dn_elimination_definable M)).
 - intros body dn d X rb rc pc pb pC ab ac result gb gc gn HB HD HR HPC HA HResult PP HM.
   apply source_dn_zero in HD. subst dn.
   assert(HOther:numerical_substitution M body rb rc(code_numeral M 2)(code_numeral M 2)result).
   { apply(numerical_prefix_substitution_compare M body(code_numeral M 2)ab ac result rb rc
      (code_numeral M 2)(code_numeral M 2)HB HResult).
     intros i v HI HV.
     destruct(source_numeral_initial_segment M 2 i HI)as(j&HJ&->).
     destruct j as[|[|j]];try lia.
     - assert(E:v=d)by(eapply substitution_lookup_functional;[exact HV|
         exact(source_dn_assignment_zero M _ _ _ _ _ _ _ HA)]). subst v.
       apply(proj2(substitution_lookup_inside M rb rc(code_numeral M 2)(code_numeral M 2)
        (zeroM M)d(coding_zero_lt_succ M(code_numeral M 1)))).
       exact(proj1(substitution_lookup_inside M rb rc(code_numeral M 2)(zeroM M)
        (zeroM M)d(coding_zero_lt_succ M(code_numeral M 1)))(proj1 HR)).
     - assert(E:v=X)by(eapply substitution_lookup_functional;[exact HV|
         exact(source_dn_assignment_one M _ _ _ _ _ _ _ HA)]). subst v.
       apply(proj2(substitution_lookup_inside M rb rc(code_numeral M 2)(code_numeral M 2)
        (code_numeral M 1)X(coding_lt_succ M(code_numeral M 1)))).
       exact(proj1(substitution_lookup_inside M rb rc(code_numeral M 2)(zeroM M)
        (code_numeral M 1)X(coding_lt_succ M(code_numeral M 1)))(proj2 HR)). }
   assert(E:result=pc)by(eapply numerical_substitution_functional;eassumption). now subst result.
 - intros count IH body dn d X rb rc pc pb pC ab ac result gb gc gn HB HD HR HPC HA HResult PP HM.
   destruct(proj1(source_dn_succ_first M count body dn)HD)as(first&HFirst&HDN).
   pose proof(source_dn_successor_bounded M body first count HB HFirst)as HFirstB.
   destruct(source_dn_environment_uncons M pb pC count)as(head&tb&tc&HT).
   destruct(source_dn_assignment_total M count tb tc d X)as(fb&fc&HFA).
   destruct(numerical_substitution_total M first fb fc(succM M(succM M count))(zeroM M))as(instance&HInstance).
   assert(HMembers:source_dn_parameter_proofs M count tb tc X gb gc gn).
   { intros i value member HI HE HMember. apply(HM(succM M i)value member);
      [exact(proj2(coding_lt_succ_cancel M i count)HI)| |exact HMember].
     apply(proj1(environment_lookup_inside M pb pC(succM M count)(succM M i)value
      (proj2(coding_lt_succ_cancel M i count)HI))).
     apply(proj2(environment_cons_tail M _ _ _ _ _ _ _ _ _ HT)).
     exact(proj2(environment_lookup_inside M tb tc count i value HI)HE). }
   pose proof(IH first dn d X rb rc pc tb tc fb fc instance gb gc gn
    HFirstB HDN HR HPC HFA HInstance PP HMembers)as PFirst.
   apply(source_full_dn_first_parameter M count pb pC head tb tc d X fb fc ab ac
    body first instance result gb gc gn HT HFA HA HB HFirst HInstance HResult PFirst).
   intros member HMember. apply(HM(zeroM M)head member);[apply coding_zero_lt_succ| |exact HMember].
   apply(proj1(environment_lookup_inside M pb pC(succM M count)(zeroM M)head(coding_zero_lt_succ M count))).
   exact(proj2(environment_cons_head M _ _ _ _ _ _ _ _ HT)eq_refl).
Qed.
Print Assumptions source_full_dn_elimination.
