(** Constructor-level interface to the canonical representation point. *)
From PAModel Require Import Model CodeExpressions SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds
 SourceRepresentationRecipe SourceIffGraphs.
Unset Implicit Arguments.
Theorem source_iff_expression_graph M rho A B a b out:
 code_relation M rho A a->code_relation M rho B b->
 (source_iff_graph M a b out<->code_relation M rho(E_sf_iff A B)out).
Proof.
 intros HA HB. split.
 - intro H. destruct(source_iff_parts M a b out H)as(lr&rl&HL&HR&HO).
   assert(GL:code_relation M rho(E_sf SFImpl A B)lr)by(exact(proj2(schema_expression_graph M rho SFImpl A B a b lr HA HB)HL)).
   assert(GR:code_relation M rho(E_sf SFImpl B A)rl)by(exact(proj2(schema_expression_graph M rho SFImpl B A b a rl HB HA)HR)).
   exact(proj2(schema_expression_graph M rho SFAnd _ _ lr rl out GL GR)HO).
 - intro H. destruct(source_iff_total M a b)as(candidate&HC).
   assert(GC:code_relation M rho(E_sf_iff A B)candidate).
   { destruct(source_iff_parts M a b candidate HC)as(lr&rl&HL&HR&HO).
     assert(GL:code_relation M rho(E_sf SFImpl A B)lr)by(exact(proj2(schema_expression_graph M rho SFImpl A B a b lr HA HB)HL)).
     assert(GR:code_relation M rho(E_sf SFImpl B A)rl)by(exact(proj2(schema_expression_graph M rho SFImpl B A b a rl HB HA)HR)).
     exact(proj2(schema_expression_graph M rho SFAnd _ _ lr rl candidate GL GR)HO). }
   rewrite(code_relation_functional M _ rho out candidate H GC). exact HC.
Qed.
Theorem source_representation_point_join M guard atom mem equiv inner point:
 sf_relation M SFMember(zeroM M)(code_numeral M 1)mem->source_iff_graph M mem atom equiv->
 sf_relation M SFImpl guard equiv inner->sf_relation M SFAll inner(zeroM M)point->
 code_relation M(representation_point_environment guard atom)(E_representation_point(CEvar 0)(CEvar 1))point.
Proof.
 intros HM HE HI HP. set(rho:=representation_point_environment guard atom).
 assert(GM:code_relation M rho(E_sf SFMember(CEconst 0)(CEconst 1))mem).
 { exact(proj2(schema_expression_graph M rho SFMember(CEconst 0)(CEconst 1)(zeroM M)(code_numeral M 1)mem eq_refl eq_refl)HM). }
 pose proof(proj1(source_iff_expression_graph M rho(E_sf SFMember(CEconst 0)(CEconst 1))(CEvar 1)mem atom equiv GM eq_refl)HE)as GE.
 exact(proj2(schema_expression_graph M rho SFAll _ (CEconst 0)inner(zeroM M)point
  (proj2(schema_expression_graph M rho SFImpl(CEvar 0)_ guard equiv inner eq_refl GE)HI)eq_refl)HP).
Qed.
Theorem source_representation_point_parts M guard atom point:
 code_relation M(representation_point_environment guard atom)(E_representation_point(CEvar 0)(CEvar 1))point->
 exists mem equiv inner,sf_relation M SFMember(zeroM M)(code_numeral M 1)mem/\source_iff_graph M mem atom equiv/\
 sf_relation M SFImpl guard equiv inner/\sf_relation M SFAll inner(zeroM M)point.
Proof.
 intro H. destruct(sf_relation_total M SFMember(zeroM M)(code_numeral M 1))as(mem&HM).
 destruct(source_iff_total M mem atom)as(equiv&HE).
 destruct(sf_relation_total M SFImpl guard equiv)as(inner&HI).
 destruct(sf_relation_total M SFAll inner(zeroM M))as(point'&HP).
 pose proof(source_representation_point_join M guard atom mem equiv inner point' HM HE HI HP)as HG.
 assert(E:point'=point)by(eapply code_relation_functional;eassumption). subst point'.
 exists mem,equiv,inner. repeat split;assumption.
Qed.
Print Assumptions source_iff_expression_graph.
Print Assumptions source_representation_point_parts.
