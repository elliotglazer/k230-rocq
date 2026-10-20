(** A genuine unary instance is also a representative-name replacement.
    Only its actual one-free-variable source bound is used. *)
From PAModel Require Import Model CodeExpressions SourceBounded NumericalInstantiation
 SourceDomainInstances SourceUnaryRenamingGraph SourceRepresentativeRenaming.
Unset Implicit Arguments.
Theorem source_unary_instance_representative M p x out:
 source_bounded M p(code_numeral M 1)->numerical_instantiation M p x out->source_representative_renaming M x p out.
Proof.
 intros BP HI. exact(source_unary_instance_renaming_graph M p(zeroM M)p x x(code_numeral M 1)(zeroM M)x out
   BP(source_domain_instance_zero M p BP)(representative_lookup_zero M x)HI).
Qed.
Print Assumptions source_unary_instance_representative.
