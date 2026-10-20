(** Exact finite selector syntax under both class and moving-set
    relativization. Arbitrary matrix holes are transformed by the genuine
    recursive graphs. There are no reflection or provability premises. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourcePropositionalTemplates SourceReflectionSelectors SourceReflectedExistential
  SourceRelativization SourceRelativizationFunctionality SourceSetRelativization
  SourceSetRelativizationFunctionality.
Unset Implicit Arguments.

Theorem source_prop_relativization M domain rho sigma a :
  (forall i,source_relativization M domain (rho i)(sigma i)) ->forall f g,
  code_relation M rho (source_prop_expression a) f ->
  code_relation M sigma (source_prop_expression a) g ->source_relativization M domain f g.
Proof.
  intro HH. induction a;intros f g HF HG.
  - change(f=rho n) in HF. change(g=sigma n) in HG. subst f g. apply HH.
  - change(f=zeroM M) in HF. change(g=zeroM M) in HG. subst f g. apply source_relativization_falsity.
  - destruct(source_prop_template_binary M rho SFImpl a1 a2 f HF) as(x&y&HX&HY&HOut).
    destruct(source_prop_template_binary M sigma SFImpl a1 a2 g HG) as(u&v&HU&HV&HOut').
    exact(source_relativization_binary M domain SFImpl x y f u v g
      (or_intror(or_intror eq_refl)) HOut (IHa1 x u HX HU)(IHa2 y v HY HV) HOut').
  - destruct(source_prop_template_binary M rho SFAnd a1 a2 f HF) as(x&y&HX&HY&HOut).
    destruct(source_prop_template_binary M sigma SFAnd a1 a2 g HG) as(u&v&HU&HV&HOut').
    exact(source_relativization_binary M domain SFAnd x y f u v g
      (or_introl eq_refl) HOut (IHa1 x u HX HU)(IHa2 y v HY HV) HOut').
  - destruct(source_prop_template_binary M rho SFOr a1 a2 f HF) as(x&y&HX&HY&HOut).
    destruct(source_prop_template_binary M sigma SFOr a1 a2 g HG) as(u&v&HU&HV&HOut').
    exact(source_relativization_binary M domain SFOr x y f u v g
      (or_intror(or_introl eq_refl)) HOut (IHa1 x u HX HU)(IHa2 y v HY HV) HOut').
Qed.

Theorem source_prop_set_relativization M name rho sigma a :
  (forall i,source_set_relativization M name (rho i)(sigma i)) ->forall f g,
  code_relation M rho (source_prop_expression a) f ->
  code_relation M sigma (source_prop_expression a) g ->source_set_relativization M name f g.
Proof.
  intro HH. induction a;intros f g HF HG.
  - change(f=rho n) in HF. change(g=sigma n) in HG. subst f g. apply HH.
  - change(f=zeroM M) in HF. change(g=zeroM M) in HG. subst f g. apply source_set_relativization_falsity.
  - destruct(source_prop_template_binary M rho SFImpl a1 a2 f HF) as(x&y&HX&HY&HOut).
    destruct(source_prop_template_binary M sigma SFImpl a1 a2 g HG) as(u&v&HU&HV&HOut').
    exact(source_set_relativization_binary M name SFImpl x y f u v g
      (or_intror(or_intror eq_refl)) HOut (IHa1 x u HX HU)(IHa2 y v HY HV) HOut').
  - destruct(source_prop_template_binary M rho SFAnd a1 a2 f HF) as(x&y&HX&HY&HOut).
    destruct(source_prop_template_binary M sigma SFAnd a1 a2 g HG) as(u&v&HU&HV&HOut').
    exact(source_set_relativization_binary M name SFAnd x y f u v g
      (or_introl eq_refl) HOut (IHa1 x u HX HU)(IHa2 y v HY HV) HOut').
  - destruct(source_prop_template_binary M rho SFOr a1 a2 f HF) as(x&y&HX&HY&HOut).
    destruct(source_prop_template_binary M sigma SFOr a1 a2 g HG) as(u&v&HU&HV&HOut').
    exact(source_set_relativization_binary M name SFOr x y f u v g
      (or_intror(or_introl eq_refl)) HOut (IHa1 x u HX HU)(IHa2 y v HY HV) HOut').
Qed.

Definition source_selector_graph M test a b out :=code_relation M
  (source_reflection_five_env test a b a b)(source_prop_expression source_reflection_pair_left) out.

Theorem source_selector_class_components M domain test a b raw out :
  source_relativization M domain test test ->source_selector_graph M test a b raw ->
  source_relativization M domain raw out ->exists ra rb,
    source_relativization M domain a ra /\source_relativization M domain b rb /\
    source_selector_graph M test ra rb out.
Proof.
  intros HTest HRaw HOut.
  destruct(source_relativization_total M domain a) as(ra&HA).
  destruct(source_relativization_total M domain b) as(rb&HB).
  destruct(code_relation_total M (source_prop_expression source_reflection_pair_left)
    (source_reflection_five_env test ra rb ra rb)) as(g&HG).
  assert(HR:source_relativization M domain raw g).
  { apply(source_prop_relativization M domain
      (source_reflection_five_env test a b a b)(source_reflection_five_env test ra rb ra rb)
      source_reflection_pair_left).
    - intros[|[|[|[|[|i]]]]];cbn[source_reflection_five_env];assumption.
    - exact HRaw.
    - exact HG. }
  pose proof(source_relativization_functional M raw domain g out HR HOut) as E. subst g.
  exists ra,rb. auto.
Qed.

Theorem source_selector_set_components M name test a b raw out :
  source_set_relativization M name test test ->source_selector_graph M test a b raw ->
  source_set_relativization M name raw out ->exists ra rb,
    source_set_relativization M name a ra /\source_set_relativization M name b rb /\
    source_selector_graph M test ra rb out.
Proof.
  intros HTest HRaw HOut.
  destruct(source_set_relativization_total M name a) as(ra&HA).
  destruct(source_set_relativization_total M name b) as(rb&HB).
  destruct(code_relation_total M (source_prop_expression source_reflection_pair_left)
    (source_reflection_five_env test ra rb ra rb)) as(g&HG).
  assert(HR:source_set_relativization M name raw g).
  { apply(source_prop_set_relativization M name
      (source_reflection_five_env test a b a b)(source_reflection_five_env test ra rb ra rb)
      source_reflection_pair_left).
    - intros[|[|[|[|[|i]]]]];cbn[source_reflection_five_env];assumption.
    - exact HRaw.
    - exact HG. }
  pose proof(source_set_relativization_functional M raw name g out HR HOut) as E. subst g.
  exists ra,rb. auto.
Qed.

Print Assumptions source_prop_relativization.
Print Assumptions source_prop_set_relativization.
Print Assumptions source_selector_class_components.
Print Assumptions source_selector_set_components.
