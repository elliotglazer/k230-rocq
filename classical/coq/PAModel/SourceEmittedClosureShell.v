(** Unpack the exact canonical emitted closure without interpreting its matrix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SetSchemaConstructors SchemaConstructorBounds SourceWFSeparationConstructor SourcePropositionalRebase
  SourceEmittedClosureRecipe.
Unset Implicit Arguments.

Theorem source_emitted_closure_shell M rho a b c out :
  code_relation M rho (CEvar 0) a ->code_relation M rho (CEvar 1) b ->
  code_relation M rho (CEvar 2) c ->
  code_relation M rho (E_source_emitted_closure (CEvar 0)(CEvar 1)(CEvar 2)) out ->
  exists xc exP pair allU subset uimp allY yimp exZ final selected outerimp,
    sf_relation M SFMember (zeroM M)(code_numeral M 1) xc /\
    sf_relation M SFMember (zeroM M)(code_numeral M 5) selected /\
    sf_relation M SFAnd c selected final /\sf_relation M SFEx final (zeroM M) exZ /\
    sf_relation M SFImpl b exZ yimp /\sf_relation M SFAll yimp (zeroM M) allY /\
    code_relation M rho E_native_subset02 subset /\
    sf_relation M SFImpl subset allY uimp /\sf_relation M SFAll uimp (zeroM M) allU /\
    sf_relation M SFAnd a allU pair /\sf_relation M SFEx pair (zeroM M) exP /\
    sf_relation M SFImpl xc exP outerimp /\sf_relation M SFAll outerimp (zeroM M) out.
Proof.
  intros H0 H1 H2 HO.
  destruct (schema_expression_quantifier_split M rho SFAll _ out HO) as [outerimp [HI HAll]].
  destruct (schema_expression_split M rho SFImpl _ _ outerimp HI) as [xc [exP [HX [HP HImp]]]].
  destruct (schema_expression_quantifier_split M rho SFEx _ exP HP) as [pair [HAP HExP]].
  destruct (schema_expression_split M rho SFAnd _ _ pair HAP) as [a' [allU [HA [HU HAnd]]]].
  pose proof (code_relation_functional M (CEvar 0) rho a' a HA H0) as E. subst a'.
  destruct (schema_expression_quantifier_split M rho SFAll _ allU HU) as [uimp [HUI HAllU]].
  destruct (schema_expression_split M rho SFImpl _ _ uimp HUI) as [subset [allY [HS [HY HImpU]]]].
  destruct (schema_expression_quantifier_split M rho SFAll _ allY HY) as [yimp [HYI HAllY]].
  destruct (schema_expression_split M rho SFImpl _ _ yimp HYI) as [b' [exZ [HB [HZ HImpY]]]].
  pose proof (code_relation_functional M (CEvar 1) rho b' b HB H1) as E. subst b'.
  destruct (schema_expression_quantifier_split M rho SFEx _ exZ HZ) as [final [HF HExZ]].
  destruct (schema_expression_split M rho SFAnd _ _ final HF) as [c' [selected [HC [HM HAndZ]]]].
  pose proof (code_relation_functional M (CEvar 2) rho c' c HC H2) as E. subst c'.
  exists xc,exP,pair,allU,subset,uimp,allY,yimp,exZ,final,selected,outerimp.
  split.
  - exact (proj1 (schema_expression_graph M rho SFMember (CEconst 0)(CEconst 1)
      (zeroM M)(code_numeral M 1) xc eq_refl eq_refl) HX).
  - split.
    + exact (proj1 (schema_expression_graph M rho SFMember (CEconst 0)(CEconst 5)
        (zeroM M)(code_numeral M 5) selected eq_refl eq_refl) HM).
    + repeat split;assumption.
Qed.

Print Assumptions source_emitted_closure_shell.
