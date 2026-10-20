(** Exact arithmetic syntax of inequivalence of two numeral predicates. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes NumericalInstantiation.
Unset Implicit Arguments.
Definition source_numf_distinct_recipe M p q x y out:=exists px qy equal neg inner,
 numerical_instantiation M p x px /\numerical_instantiation M q y qy /\sf_relation M SFEqual x y equal /\
 sf_relation M SFImpl equal(zeroM M)neg /\sf_relation M SFImpl qy neg inner /\sf_relation M SFImpl px inner out.
Theorem source_numf_distinct_recipe_total M p q x y:exists out,source_numf_distinct_recipe M p q x y out.
Proof.
 destruct(numerical_instantiation_total M p x)as(px&HX). destruct(numerical_instantiation_total M q y)as(qy&HY).
 destruct(sf_relation_total M SFEqual x y)as(equal&HE). destruct(sf_relation_total M SFImpl equal(zeroM M))as(neg&HN).
 destruct(sf_relation_total M SFImpl qy neg)as(inner&HI). destruct(sf_relation_total M SFImpl px inner)as(out&HO).
 exists out,px,qy,equal,neg,inner. repeat split;assumption.
Qed.
Print Assumptions source_numf_distinct_recipe_total.
