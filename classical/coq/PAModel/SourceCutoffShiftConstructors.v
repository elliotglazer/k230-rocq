(** Actual constructor laws for the fixed-cutoff numerical substitutions. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SetCodeDescent
  NumericalSubstitutionMaps NumericalSubstitution SourceFiniteCutoffShift SourceQfFunctionality.
Unset Implicit Arguments.

Theorem source_cutoff_shift_binary M depth h a b f a' b' g :
  sf_binary h ->sf_relation M h a b f ->sf_relation M h a' b' g ->
  source_cutoff_shift M depth a a' ->source_cutoff_shift M depth b b' ->source_cutoff_shift M depth f g.
Proof.
  intros HH HF HG(ab&ac&an&HAMap&HA)(bb&bc&bn&HBMap&HB).
  exists ab,ac,an. split;[exact HAMap|].
  apply(proj2(numerical_substitution_binary M h a b f ab ac an(code_numeral M(S depth))g HH HF)).
  exists a',b'. split;[exact HA|]. split;[|exact HG].
  apply(proj1(numerical_substitution_extensional M b bb bc bn ab ac an(code_numeral M(S depth))b'
    (source_cutoff_shift_maps_equivalent M depth bb bc bn ab ac an HBMap HAMap))). exact HB.
Qed.
Theorem source_cutoff_shift_fixed_member M depth i j f g :
  sf_relation M SFMember(code_numeral M i)(code_numeral M j)f ->
  sf_relation M SFMember(code_numeral M(sf_index(source_shift_sigma depth i)))
    (code_numeral M(sf_index(source_shift_sigma depth j)))g ->source_cutoff_shift M depth f g.
Proof.
  intros HF HG. destruct(source_cutoff_shift_map_total M depth) as(b&c&n&HM).
  exists b,c,n. split;[exact HM|].
  apply(proj2(numerical_substitution_member M(code_numeral M i)(code_numeral M j)f b c n(code_numeral M(S depth))g HF)).
  exists(code_numeral M(sf_index(source_shift_sigma depth i))),(code_numeral M(sf_index(source_shift_sigma depth j))).
  split;[exact(source_cutoff_shift_map_fixed_lookup M depth b c n HM i)|].
  split;[exact(source_cutoff_shift_map_fixed_lookup M depth b c n HM j)|exact HG].
Qed.
Print Assumptions source_cutoff_shift_binary.
Print Assumptions source_cutoff_shift_fixed_member.
