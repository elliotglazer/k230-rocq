(** Exact use of the L-Separation image assumption, opened only under
    its literal parameter-domain table. No Replacement image is assumed. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
 NumericalZFCAxioms NumericalZFCClosure NumericalSetClosure SchemaRenamingDescriptors SetSchemaConstructors SchemaConstructorBounds SchemaRenamingBounds
 SourceKZFCForwardSchemas SourceLFixed SourceRelativization SourceRelativeSchemaConstructors SourceSchemaRelativization
 SourceGuardedDomainOpening SourceDomainContexts ContextCombination NumericalContexts NumericalSourceFull SourceZFRProvability.
Unset Implicit Arguments.
Local Opaque source_L_domain_code.
Theorem source_zfr_L_separation_instance_from_images M phi count body open target:
 L_separation_image_obligation M ->source_bounded M phi(succM M count) ->
 schema_renaming M SepBody phi body ->sf_separation_constructor M body open ->
 source_relativization M(source_L_domain_code M)open target ->
 exists closed image,all_prefix M count open closed /\source_relativization M(source_L_domain_code M)closed image /\
 source_zfr_provable M image.
Proof.
 intros HS BF HB HO HT.
 destruct(all_prefix_total M count open)as(closed&HClosed).
 destruct(source_relativization_total M(source_L_domain_code M)closed)as(image&HImage).
 assert(HInstance:numerical_separation_instance M phi count closed).
 { split;[exact BF|]. exists body,open;auto. }
 exists closed,image. repeat split;try assumption.
 apply(HS closed image);[|exact HImage].
 split;[exact(numerical_separation_instance_closed M phi count closed HInstance)|]. exists phi,count;exact HInstance.
Qed.
Theorem source_full_L_separation_open_from_images M phi count body open target db dc:
 L_separation_image_obligation M ->source_bounded M phi(succM M count) ->
 schema_renaming M SepBody phi body ->sf_separation_constructor M body open ->
 source_relativization M(source_L_domain_code M)open target ->source_domain_context M(source_L_domain_code M)count db dc ->
 exists ab ac an ub uc un,source_zfr_context M ab ac an /\context_union M ab ac an db dc count ub uc un /\source_full_prv M ub uc un target.
Proof.
 intros HS BF HB HO HT HTable.
 destruct(source_zfr_L_separation_instance_from_images M phi count body open target HS BF HB HO HT)
  as(closed&image&HClosed&HImage&PImage).
 exact(source_zfr_open_relative_prefix M(source_L_domain_code M)count open target closed image db dc
  (numerical_L_domain_bounded M)(schema_separation_constructor_bound M body open count(schema_separation_bound M phi body count BF HB)HO)
  HClosed HT HImage HTable PImage).
Qed.
Print Assumptions source_zfr_L_separation_instance_from_images.
Print Assumptions source_full_L_separation_open_from_images.
