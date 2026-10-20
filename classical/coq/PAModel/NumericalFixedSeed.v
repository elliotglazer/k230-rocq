(** A prescribed seed for arbitrary internally coded KP0 matrices. The seed
    occurs in the matrix, so the generated fresh names cannot capture it. *)
From PAModel Require Import Model FiniteCoding CodeExpressions FreshNames
  NumericalProofs ProofTemplates NamedSubstitution NamedBinderFresh
  NumericalKP0Eligibility NumericalKP0Requests KP0SeedSpecialization.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Theorem numerical_uniform_kp0_fixed_seed M a b m root :
  a<>zeroM M -> b<>a -> a<>root -> b<>root ->
  named_binder_absent M m a -> named_binder_absent M m root ->
  formula_mentions M m root ->
  exists k p mp f,
    k<>a /\ k<>b /\ k<>root /\ a<>p /\ b<>p /\ k<>p /\ p<>root /\
    p<>zeroM M /\ formula_fresh M m k /\ formula_fresh M m p /\
    named_substitution M m a p mp /\
    code_relation M (kp0_seed_parameters M a b k p m mp root)
      (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2)
        (CEvar 3) (CEvar 4) (CEvar 5)) f /\
    numerically_provable M f.
Proof.
  intros H0 HBA HAR HBR HMA HMR Hmention.
  destruct (numerical_uniform_kp0 M a b m H0 HBA HMA)
    as [k [p [mp [g [HKA [HKB [HAP [HBP [HKP [HP [HMK [HMP [HS [HG PG]]]]]]]]]]]]]].
  assert (HKR:k<>root) by (intro E;apply (HMK root Hmention);symmetry;exact E).
  assert (HPR:p<>root) by (intro E;apply (HMP root Hmention);symmetry;exact E).
  set (rho:=kp0_seed_parameters M a b k p m mp root).
  assert (HG':code_relation M rho
    (E_kp_conclusion (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3) (CEvar 4) (CEvar 5)) g)
    by exact HG.
  destruct (code_relation_total M
    (E_kp_with_seed (CEvar 6) (CEvar 0) (CEvar 1) (CEvar 2)
      (CEvar 3) (CEvar 4) (CEvar 5)) rho) as [f HF].
  assert (PF:numerically_provable M f).
  { exact (numerical_kp0_with_seed M a b k p m mp root g f
      H0 HAP HBA HKA HAR HBR HKR HPR HMA HMR HS HG' HF PG). }
  exists k,p,mp,f. repeat split;assumption.
Qed.

Print Assumptions numerical_uniform_kp0_fixed_seed.
