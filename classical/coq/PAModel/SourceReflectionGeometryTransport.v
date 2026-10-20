(** Actual numerical substitutions of all fixed reflection geometry leaves. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalSubstitutionMaps NumericalSubstitution
 SourceReflectionGeometryPredicates SourceFiniteParameters SourceFiniteNameParameters SourceParameterTransport SourceCofinalGeometry.
From Stdlib Require Import Lia Arith.PeanoNat.
Unset Implicit Arguments.
Theorem source_reflection_geometry_substitution M tag rho rho' old new rb rc rn base:
 source_reflection_geometry_instance M tag rho old ->source_reflection_geometry_instance M tag rho' new ->
 (forall i,(i<source_reflection_geometry_arity tag)%nat ->substitution_lookup M rb rc rn base(rho i)(rho' i)) ->
 numerical_substitution M old rb rc rn base new.
Proof.
 intros HO HN HNames.
 apply(source_parameter_transport M(source_reflection_geometry_arity tag)(source_reflection_geometry_source tag)
  (source_reflection_geometry_finite_bound tag)(source_finite_parameter_names(source_reflection_geometry_arity tag))
  (source_finite_parameter_names(source_reflection_geometry_arity tag))rho rho' rb rc rn base old new);[|exact HO|exact HN].
 intros i x y HI HX HY. unfold source_finite_parameter_names in HX,HY.
 assert(E:Nat.ltb i(source_reflection_geometry_arity tag)=true)by(now apply Nat.ltb_lt).
 rewrite E in HX,HY. change(x=rho i)in HX. change(y=rho' i)in HY. subst x y. exact(HNames i HI).
Qed.
Theorem source_cofinal_ordinals_substitution M K old K' new rb rc rn base:
 source_cofinal_ordinals M K old ->source_cofinal_ordinals M K' new ->substitution_lookup M rb rc rn base K K' ->
 numerical_substitution M old rb rc rn base new.
Proof.
 intros HO HN HK. apply(source_parameter_transport M 1 source_cofinal_ordinals_predicate source_cofinal_ordinals_finite_bound
  (source_finite_parameter_names 1)(source_finite_parameter_names 1)(fun _=>K)(fun _=>K')rb rc rn base old new);[|exact HO|exact HN].
 intros[|i]x y HI HX HY;[|lia]. change(x=K)in HX. change(y=K')in HY. now subst x y.
Qed.
Print Assumptions source_reflection_geometry_substitution.
Print Assumptions source_cofinal_ordinals_substitution.
