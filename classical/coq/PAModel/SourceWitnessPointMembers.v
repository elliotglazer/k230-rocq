(** The actual positive-point assignment shares the diagonal assignment's
 tail, shifted once. Only its quantified output is a new live name. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes
 NumericalEnvironments NumericalSubstitutionMaps NumericalRenamingMaps NumericalRenaming NumericalContextRenaming
 SourceWitnessThetaInstances NumericalSourceFull SourceProofRenaming SourceQuantifierRules NumericalContexts.
From Stdlib Require Import Lia.
Unset Implicit Arguments.
Theorem source_witness_point_lookup_cases M p s t delta db dc pb pc i name:
 source_witness_diagonal_map M p delta db dc->source_witness_point_map M p s t delta pb pc->
 substitution_lookup M pb pc(code_numeral M 4)(succM M delta)i name->
 name=zeroM M \/name=succM M p \/name=succM M s \/name=succM M t \/
 exists old,substitution_lookup M db dc(code_numeral M 4)delta i old /\name=succM M old.
Proof.
 intros HD HP HName. destruct(environment_lt_cases M i(code_numeral M 4))as[HI|HI].
 - change(coding_lt M i(succM M(succM M(succM M(succM M(zeroM M))))))in HI.
   apply coding_lt_succ_cases in HI as[HI|E];[|subst i;right;right;right;left;exact(substitution_lookup_functional M _ _ _ _ _ name _ HName(HP 3 ltac:(lia)))].
   apply coding_lt_succ_cases in HI as[HI|E];[|subst i;right;right;left;exact(substitution_lookup_functional M _ _ _ _ _ name _ HName(HP 2 ltac:(lia)))].
   apply coding_lt_succ_cases in HI as[HI|E];[|subst i;right;left;exact(substitution_lookup_functional M _ _ _ _ _ name _ HName(HP 1 ltac:(lia)))].
   apply coding_lt_succ_cases in HI as[HI|E];[exfalso;exact(coding_not_lt_zero M i HI)|].
   subst i. left. exact(substitution_lookup_functional M _ _ _ _ _ name _ HName(HP 0 ltac:(lia))).
 - apply substitution_lookup_outside in HName;[|exact HI]. destruct HName as(j&EI&EN).
   right;right;right;right. exists(addM M delta j). split.
   + apply(proj2(substitution_lookup_outside M db dc(code_numeral M 4)delta i(addM M delta j)HI)). exists j. auto.
   + rewrite EN,Arithmetic.add_succ. reflexivity.
Qed.
Theorem source_full_shifted_member M gb gc gn sb sc x Y old member:
 context_shift M gb gc gn sb sc->sf_relation M SFMember x Y old->
 sf_relation M SFMember(succM M x)(succM M Y)member->
 source_full_prv M gb gc gn old->source_full_prv M sb sc gn member.
Proof.
 intros HS HO HM PO. apply(source_full_prv_renaming M gb gc gn old(zeroM M)(zeroM M)(zeroM M)
  (code_numeral M 1)sb sc member PO HS).
 apply(proj2(numerical_renaming_member M x Y old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)member HO)).
 exists(succM M x),(succM M Y). split;[apply context_shift_lookup;reflexivity|].
 split;[apply context_shift_lookup;reflexivity|exact HM].
Qed.
Print Assumptions source_witness_point_lookup_cases.
Print Assumptions source_full_shifted_member.
