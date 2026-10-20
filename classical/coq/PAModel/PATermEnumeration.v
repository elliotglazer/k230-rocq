(** An explicit total enumeration of the pinned arithmetic term carrier.
    The library's constructive optional enumeration is totalized by zero.
    No choice, extensionality, quotient, or equality axiom is used. *)
From Stdlib Require Import List Cantor Vectors.Vector.
From Undecidability.FOL.Arithmetics Require Import Signature.
From Undecidability.FOL.Syntax Require Import DiscreteEnumerable.
From Undecidability.Synthetic Require Import EnumerabilityFacts ListEnumerabilityFacts.
Import ListNotations.
Unset Implicit Arguments.

Definition pa_function_list (n:nat) : list PA_funcs :=
 match enum_PA_funcs n with Some f=>[f]|None=>[]end.
Lemma pa_function_list_enumerates : list_enumerator__T pa_function_list PA_funcs.
Proof.
 intro f. destruct(enumerator_PA_funcs f)as(n&Hn). exists n.
 unfold pa_function_list. rewrite Hn. now left.
Qed.
Definition pa_term_list : nat ->list(@term PA_funcs_signature) :=
 @L_term PA_funcs_signature pa_function_list pa_function_list_enumerates.
Definition pa_term_optional (n:nat) : option(@term PA_funcs_signature) :=
 let '(level,position):=Cantor.of_nat n in List.nth_error(pa_term_list level)position.
Lemma pa_term_optional_enumerates : enumerator__T pa_term_optional (@term PA_funcs_signature).
Proof.
 intro t. apply(proj2(list_enumerator_to_enumerator _ pa_term_list t)).
 exact(@enum_term PA_funcs_signature pa_function_list pa_function_list_enumerates t).
Qed.
Definition pa_term_enumerate (n:nat) : @term PA_funcs_signature :=
 match pa_term_optional n with
 |Some t=>t
 |None=>@func PA_funcs_signature Zero (Vector.nil _)
 end.
Theorem pa_term_enumerate_surjective :forall t:@term PA_funcs_signature,
 exists n,pa_term_enumerate n=t.
Proof.
 intro t. destruct(pa_term_optional_enumerates t)as(n&Hn).
 exists n. unfold pa_term_enumerate. now rewrite Hn.
Qed.
Theorem pa_terms_countable :exists enumerate:nat ->@term PA_funcs_signature,
 forall t,exists n,enumerate n=t.
Proof. exists pa_term_enumerate. exact pa_term_enumerate_surjective. Qed.
Print Assumptions pa_function_list_enumerates.
Print Assumptions pa_term_optional_enumerates.
Print Assumptions pa_term_enumerate_surjective.
Print Assumptions pa_terms_countable.
