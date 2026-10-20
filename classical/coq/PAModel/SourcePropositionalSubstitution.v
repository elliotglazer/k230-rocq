(** Actual substitution through a fixed propositional expression with
    arbitrary internally coded formula holes. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  NumericalSubstitutionMaps NumericalSubstitution SchemaConstructorBounds
  SourcePropositionalTemplates SourcePropositionalRebase.
Unset Implicit Arguments.

Theorem source_prop_expression_substitution M env env' b c n base a :
  (forall i,numerical_substitution M (env i) b c n base (env' i)) ->
  forall f g,code_relation M env (source_prop_expression a) f ->
    code_relation M env' (source_prop_expression a) g ->
    numerical_substitution M f b c n base g.
Proof.
  intro HH. induction a;intros f g HF HG;cbn [source_prop_expression] in HF,HG.
  - change (f=env n0) in HF. change (g=env' n0) in HG. subst f g. apply HH.
  - change (f=zeroM M) in HF. change (g=zeroM M) in HG. subst f g.
    apply (proj2 (numerical_substitution_invalid M (zeroM M) b c n base (zeroM M) (or_introl eq_refl))). reflexivity.
  - destruct (schema_expression_split M env SFImpl _ _ f HF) as [x [y [HX [HY HXY]]]].
    destruct (schema_expression_split M env' SFImpl _ _ g HG) as [u [v [HU [HV HUV]]]].
    apply (proj2 (numerical_substitution_binary M SFImpl x y f b c n base g
      (or_intror (or_intror eq_refl)) HXY)).
    exists u,v. split;[exact (IHa1 x u HX HU)|]. split;[exact (IHa2 y v HY HV)|exact HUV].
  - destruct (schema_expression_split M env SFAnd _ _ f HF) as [x [y [HX [HY HXY]]]].
    destruct (schema_expression_split M env' SFAnd _ _ g HG) as [u [v [HU [HV HUV]]]].
    apply (proj2 (numerical_substitution_binary M SFAnd x y f b c n base g
      (or_introl eq_refl) HXY)).
    exists u,v. split;[exact (IHa1 x u HX HU)|]. split;[exact (IHa2 y v HY HV)|exact HUV].
  - destruct (schema_expression_split M env SFOr _ _ f HF) as [x [y [HX [HY HXY]]]].
    destruct (schema_expression_split M env' SFOr _ _ g HG) as [u [v [HU [HV HUV]]]].
    apply (proj2 (numerical_substitution_binary M SFOr x y f b c n base g
      (or_intror (or_introl eq_refl)) HXY)).
    exists u,v. split;[exact (IHa1 x u HX HU)|]. split;[exact (IHa2 y v HY HV)|exact HUV].
Qed.

Print Assumptions source_prop_expression_substitution.
