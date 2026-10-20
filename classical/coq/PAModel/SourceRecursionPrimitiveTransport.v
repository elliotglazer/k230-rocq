(** Actual capture-avoiding substitution of named recursion primitives. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation
  SourceFiniteParameters SourceFiniteNameParameters SourceParameterTransport SourceRecursionPrimitiveRelations SubstitutionSource.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Theorem source_rec_app_functional M f u v a b:source_rec_app M f u v a ->source_rec_app M f u v b ->a=b.
Proof. exact(code_relation_functional M _ _ a b). Qed.
Theorem source_rec_successor_functional M u v a b:source_rec_successor M u v a ->source_rec_successor M u v b ->a=b.
Proof. exact(code_relation_functional M _ _ a b). Qed.

Theorem source_rec_app_substitution M f u v out f' u' v' out' rb rc rn base:
  source_rec_app M f u v out ->source_rec_app M f' u' v' out' ->
  substitution_lookup M rb rc rn base f f' ->substitution_lookup M rb rc rn base u u' ->substitution_lookup M rb rc rn base v v' ->
  numerical_substitution M out rb rc rn base out'.
Proof.
  intros HO HO' HF HU HV.
  apply(source_parameter_transport M 3 source_rec_app_predicate source_rec_app_finite_bound(source_finite_parameter_names 3)(source_finite_parameter_names 3)
    (source_rec_env3 f u v)(source_rec_env3 f' u' v')rb rc rn base out out');[|exact HO|exact HO'].
  intros[|[|[|i]]] x y HI HX HY;try lia.
  - change(x=f)in HX. change(y=f')in HY. now subst x y.
  - change(x=u)in HX. change(y=u')in HY. now subst x y.
  - change(x=v)in HX. change(y=v')in HY. now subst x y.
Qed.
Theorem source_rec_successor_substitution M u v out u' v' out' rb rc rn base:
  source_rec_successor M u v out ->source_rec_successor M u' v' out' ->
  substitution_lookup M rb rc rn base u u' ->substitution_lookup M rb rc rn base v v' ->
  numerical_substitution M out rb rc rn base out'.
Proof.
  intros HO HO' HU HV.
  apply(source_parameter_transport M 2 source_rec_successor_predicate source_rec_successor_finite_bound(source_finite_parameter_names 2)(source_finite_parameter_names 2)
    (source_rec_env2 u v)(source_rec_env2 u' v')rb rc rn base out out');[|exact HO|exact HO'].
  intros[|[|i]] x y HI HX HY;try lia.
  - change(x=u)in HX. change(y=u')in HY. now subst x y.
  - change(x=v)in HX. change(y=v')in HY. now subst x y.
Qed.

Theorem source_rec_app_instantiation M f u old v out:
  source_rec_app M(succM M f)(succM M u)(zeroM M)old ->source_rec_app M f u v out ->
  numerical_instantiation M old v out.
Proof.
  intros HO HG. destruct(substitution_singleton_total M v) as(rb&rc&HHead&_). exists rb,rc. split;[exact HHead|].
  exact(source_rec_app_substitution M(succM M f)(succM M u)(zeroM M)old f u v out rb rc(code_numeral M 1)(zeroM M)
    HO HG(substitution_singleton_tail M rb rc f)(substitution_singleton_tail M rb rc u)HHead).
Qed.

Print Assumptions source_rec_app_functional.
Print Assumptions source_rec_successor_functional.
Print Assumptions source_rec_app_substitution.
Print Assumptions source_rec_successor_substitution.
Print Assumptions source_rec_app_instantiation.
