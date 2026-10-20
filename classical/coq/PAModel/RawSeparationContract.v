(** The raw-domain certificate interface consumed by the quotient/source
    transfer. ActualRawSeparationContract supplies this family from K in
    every PA model. Its syntax contains raw membership only. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalEquivalence
  NamedBinderFresh FreshNames QuotedSameContainer SeparationAllocation.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition E_raw_domain_separation A W Theta :=
  E_wim (E_wel (CEconst 1) A)
    (E_wex (CEadd A (CEconst 1))
      (E_raw_selection_container (CEconst 1) A (CEadd A (CEconst 1)) W Theta)).

Definition raw_separation_parameters M a w theta :=
  a .: w .: theta .: fun _=>zeroM M.

Definition raw_domain_separation_certificates M marker :=
  forall a w theta,
    coding_lt M (code_numeral M 1) a -> coding_lt M (separation_base M a) w ->
    formula_fresh M theta a -> formula_fresh M theta (succM M a) ->
    (forall y,coding_lt M y (succM M w) -> named_binder_absent M theta y) ->
    forall out,code_relation M (raw_separation_parameters M a w theta)
      (E_raw_domain_separation (CEvar 0) (CEvar 1) (CEvar 2)) out ->
      numerical_implies M marker out.
