(** Literal raw subset occurrences in finite parameterized hierarchy laws. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  SourceFiniteParameters SourcePropositionalRebase SchemaConstructorBounds SourceRawSubset OldNamedSyntaxBridge.
From OldZFC Require Z_base.
Unset Implicit Arguments.

Theorem source_parameter_raw_subset M names rho i j x y out :
  code_relation M rho (names i) x ->code_relation M rho (names j) y ->
  code_relation M rho (source_parameter_expression names
    (isolated_formula (OldZFC.Z_base.Sub0 (@OC.var OB.sig_empty i) (@OC.var OB.sig_empty j)))) out ->
  source_raw_subset_graph M x y out.
Proof.
  intros HX HY HO.
  change (code_relation M rho
    (E_sf SFAll (E_sf SFImpl
      (E_sf SFMember (CEconst 0) (CEadd (names i) (CEconst 1)))
      (E_sf SFMember (CEconst 0) (CEadd (names j) (CEconst 1)))) (CEconst 0)) out) in HO.
  destruct (schema_expression_split M rho _ _ _ out HO) as (point&z&HP&HZ&HAll).
  change (z=zeroM M) in HZ. subst z.
  destruct (schema_expression_split M rho _ _ _ point HP) as (left&right&HL&HR&HImp).
  assert (HXS:code_relation M rho (CEadd (names i) (CEconst 1)) (succM M x)).
  { exists x,(code_numeral M 1). split;[exact HX|]. split;[reflexivity|].
    pose proof (Arithmetic.succ_as_add M x) as E. exact E. }
  assert (HYS:code_relation M rho (CEadd (names j) (CEconst 1)) (succM M y)).
  { exists y,(code_numeral M 1). split;[exact HY|]. split;[reflexivity|].
    pose proof (Arithmetic.succ_as_add M y) as E. exact E. }
  pose proof (proj1 (schema_expression_graph M rho SFMember (CEconst 0) _ (zeroM M)
    (succM M x) left eq_refl HXS) HL) as HLeft.
  pose proof (proj1 (schema_expression_graph M rho SFMember (CEconst 0) _ (zeroM M)
    (succM M y) right eq_refl HYS) HR) as HRight.
  exists left,right,point. repeat split;assumption.
Qed.

Print Assumptions source_parameter_raw_subset.
