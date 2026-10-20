(** Identify LL occurrences inside the pinned finite hierarchy laws with
    the shared actual two-name hierarchy graph. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldFullNDSourceBridge
  SourceFiniteParameters SourceFiniteParameterComposition SourceFiniteNameParameters SourceParameterGraphs
  SourceHierarchySyntax.
From OldZFC Require Z_L.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Lemma isolated_LL_at t s :
  isolated_formula (OldZFC.Z_L.LL t s) =
  C.subst_form (C.scons (isolated_term t) (C.scons (isolated_term s) C.var)) source_LL_predicate.
Proof.
  pose proof (isolated_formula_subst
    (OldZFC.Z_L.LL (@OC.var OB.sig_empty 0) (@OC.var OB.sig_empty 1))
    (OC.scons t (OC.scons s OC.var))
    (C.scons (isolated_term t) (C.scons (isolated_term s) C.var))
    ltac:(intros [|[|i]];reflexivity)) as HE.
  rewrite OldZFC.Z_L.LL_subst in HE. exact HE.
Qed.

Theorem source_parameter_LL_instance M names rho i j d z out :
  code_relation M rho (names i) d ->code_relation M rho (names j) z ->
  code_relation M rho (source_parameter_expression names
    (isolated_formula (OldZFC.Z_L.LL (@OC.var OB.sig_empty i) (@OC.var OB.sig_empty j)))) out ->
  source_LL_instance M d z out.
Proof.
  intros HD HZ HG. rewrite isolated_LL_at,source_parameter_substitution in HG.
  assert (HNames:forall k v,(k<2)%nat ->
    (code_relation M rho (names (sf_index ((C.scons (isolated_term (@OC.var OB.sig_empty i))
      (C.scons (isolated_term (@OC.var OB.sig_empty j)) C.var)) k))) v <->
    code_relation M (fun k=>match k with 0=>d|_=>z end) (source_finite_parameter_names 2 k) v)).
  { intros [|[|k]] v HK;try lia.
    - change (code_relation M rho (names i) v <->v=d). split.
      + intro HV. exact (code_relation_functional M (names i) rho v d HV HD).
      + intros ->. exact HD.
    - change (code_relation M rho (names j) v <->v=z). split.
      + intro HV. exact (code_relation_functional M (names j) rho v z HV HZ).
      + intros ->. exact HZ. }
  exact (proj1 (source_parameter_graph_ext M 2 source_LL_predicate source_LL_predicate_finite_bound
    (fun k=>names (sf_index ((C.scons (isolated_term (@OC.var OB.sig_empty i))
      (C.scons (isolated_term (@OC.var OB.sig_empty j)) C.var)) k)))
    (source_finite_parameter_names 2) rho (fun k=>match k with 0=>d|_=>z end) HNames out) HG).
Qed.

Print Assumptions isolated_LL_at.
Print Assumptions source_parameter_LL_instance.
