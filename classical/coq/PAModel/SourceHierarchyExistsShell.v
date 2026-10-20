(** Expose the actual finite hierarchy existence law using the shared LL
    and Ord graphs, with arbitrary internally coded ordinal names. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  SourceHierarchySyntax SourceHierarchyCalibration SourceHierarchyFixed SourceHierarchyOld
  SourceFiniteParameters SourceFiniteNameParameters SourceOrdinalPredicate SourceOrdinalParameterCalibration
  SourcePropositionalRebase SourceZFRProvability NumericalInstantiation OldNamedSyntaxBridge.
Unset Implicit Arguments.
Local Opaque source_LL_predicate source_ordinal_predicate.

Definition source_hierarchy_exists_shell M d ordinal body ex law :=
  numerical_instantiation M (source_ordinal_predicate_code M) d ordinal /\
  source_LL_instance M (succM M d) (zeroM M) body /\
  sf_relation M SFEx body (zeroM M) ex /\sf_relation M SFImpl ordinal ex law.

Theorem source_zfr_hierarchy_exists_shell M d :exists ordinal body ex law,
  source_hierarchy_exists_shell M d ordinal body ex law /\source_zfr_provable M law.
Proof.
  set (rho:=fun (_:nat)=>d).
  destruct (code_relation_total M source_hierarchy_exists_expression rho) as (law&HLaw).
  pose proof (source_zfr_hierarchy_exists M rho law HLaw) as PLaw.
  unfold source_hierarchy_exists_expression,source_hierarchy_exists_law,old_hierarchy_exists_law in HLaw.
  change (code_relation M rho
    (E_sf SFImpl
      (source_parameter_expression (source_finite_parameter_names 4)
        (isolated_formula (OldZFC.Z_base.Ord0 (@OC.var OB.sig_empty 0))))
      (E_sf SFEx
        (source_parameter_expression (source_parameter_up (source_finite_parameter_names 4))
          (isolated_formula (OldZFC.Z_L.LL (@OC.var OB.sig_empty 1) (@OC.var OB.sig_empty 0))))
        (CEconst 0))) law) in HLaw.
  destruct (schema_expression_split M rho _ _ _ law HLaw) as (ordinal&ex&HOrd&HEx&HImp).
  destruct (schema_expression_split M rho _ _ _ ex HEx) as (body&z&HBody&HZ&HQuant).
  change (z=zeroM M) in HZ. subst z.
  assert (HOrdName:code_relation M rho (source_finite_parameter_names 4 0) d) by reflexivity.
  pose proof (source_parameter_ordinal_instance M (source_finite_parameter_names 4) rho 0 d ordinal
    HOrdName HOrd) as HOrdinal.
  assert (HLevelName:code_relation M rho (source_parameter_up (source_finite_parameter_names 4) 1) (succM M d)).
  { exists d,(code_numeral M 1). split;[reflexivity|]. split;[reflexivity|].
    pose proof (Arithmetic.succ_as_add M d) as E. exact E. }
  assert (HSetName:code_relation M rho (source_parameter_up (source_finite_parameter_names 4) 0) (zeroM M))
    by reflexivity.
  pose proof (source_parameter_LL_instance M (source_parameter_up (source_finite_parameter_names 4)) rho
    1 0 (succM M d) (zeroM M) body HLevelName HSetName HBody) as HLL.
  exists ordinal,body,ex,law. split;[repeat split;assumption|exact PLaw].
Qed.

Print Assumptions source_zfr_hierarchy_exists_shell.
