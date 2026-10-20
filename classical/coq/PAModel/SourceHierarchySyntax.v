(** Literal two-name hierarchy predicates, with internally arbitrary names. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded OldNamedSyntaxBridge OldFullNDSourceBridge SourceFiniteParameters
  SourceFiniteNameParameters SourceParameterGraphs SourceParameterTransport
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation RenamingSubstitution NumericalRenaming.
From OldZFC Require Z_L Z_refl Z_rel.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition source_LL_predicate :sf_form :=
  isolated_formula (OldZFC.Z_L.LL (@OC.var OB.sig_empty 0) (@OC.var OB.sig_empty 1)).
Definition source_LL_instance M d z out :=
  code_relation M (fun i=>match i with 0=>d|_=>z end)
    (source_parameter_expression (source_finite_parameter_names 2) source_LL_predicate) out.

Lemma source_LL_predicate_finite_bound :Undecidability.FOL.Syntax.Bounded.bounded 2 source_LL_predicate.
Proof.
  apply (@isolated_bounded OC.falsity_on 2
    (OldZFC.Z_L.LL (@OC.var OB.sig_empty 0) (@OC.var OB.sig_empty 1))).
  exact (OldZFC.Z_rel.fb_bounded _ 2
    (OldZFC.Z_refl.fb_LL (@OC.var OB.sig_empty 0) (@OC.var OB.sig_empty 1) 2 ltac:(cbn;lia) ltac:(cbn;lia))).
Qed.

Theorem source_LL_instance_total M d z :exists out,source_LL_instance M d z out.
Proof. apply code_relation_total. Qed.
Theorem source_LL_instance_functional M d z f g :
  source_LL_instance M d z f ->source_LL_instance M d z g ->f=g.
Proof. exact (code_relation_functional M _ _ f g). Qed.
Theorem source_LL_instance_bounded M d z out k :
  coding_lt M d k ->coding_lt M z k ->source_LL_instance M d z out ->source_bounded M out k.
Proof.
  intros HD HZ HO. apply (source_parameter_graph_bounded M 2 source_LL_predicate
    source_LL_predicate_finite_bound (source_finite_parameter_names 2)
    (fun i=>match i with 0=>d|_=>z end) k);[|exact HO].
  intros [|[|i]] x HI HX;try lia.
  - change (x=d) in HX. now subst x.
  - change (x=z) in HX. now subst x.
Qed.

Theorem source_LL_instance_substitution M d z out d' z' out' b c n base :
  source_LL_instance M d z out ->source_LL_instance M d' z' out' ->
  substitution_lookup M b c n base d d' ->substitution_lookup M b c n base z z' ->
  numerical_substitution M out b c n base out'.
Proof.
  intros HO HO' HD HZ. apply (source_parameter_transport M 2 source_LL_predicate
    source_LL_predicate_finite_bound (source_finite_parameter_names 2) (source_finite_parameter_names 2)
    (fun i=>match i with 0=>d|_=>z end) (fun i=>match i with 0=>d'|_=>z' end)
    b c n base out out');[|exact HO|exact HO'].
  intros [|[|i]] x y HI HX HY;try lia.
  - change (x=d) in HX. change (y=d') in HY. now subst x y.
  - change (x=z) in HX. change (y=z') in HY. now subst x y.
Qed.

Theorem source_LL_instance_instantiation M d z out d' z' out' t :
  source_LL_instance M d z out ->source_LL_instance M d' z' out' ->
  (forall b c,substitution_lookup M b c (succM M (zeroM M)) (zeroM M) (zeroM M) t ->
    substitution_lookup M b c (succM M (zeroM M)) (zeroM M) d d') ->
  (forall b c,substitution_lookup M b c (succM M (zeroM M)) (zeroM M) (zeroM M) t ->
    substitution_lookup M b c (succM M (zeroM M)) (zeroM M) z z') ->
  numerical_instantiation M out t out'.
Proof.
  intros HO HO' HD HZ. destruct (substitution_singleton_total M t) as (b&c&HH&HT).
  exists b,c. split;[exact HH|].
  exact (source_LL_instance_substitution M d z out d' z' out' b c (succM M (zeroM M)) (zeroM M)
    HO HO' (HD b c HH) (HZ b c HH)).
Qed.

Print Assumptions source_LL_predicate_finite_bound.
Print Assumptions source_LL_instance_total.
Print Assumptions source_LL_instance_bounded.
Print Assumptions source_LL_instance_substitution.
Print Assumptions source_LL_instance_instantiation.
