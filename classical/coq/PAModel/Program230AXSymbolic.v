(** Symbolic evaluation of the exact pre-gate AX schedule over arithmetic expressions.
 The two input reads use the supplied bound/pl4 and u/pl5 values; no run theorem is asserted here. *)
From PAModel Require Import CodeExpressions SearchStep Program230Configurations Program230AXCompactSchedule.
From Stdlib Require Import Lists.List Arith.Arith Bool.Bool.
Import ListNotations.
Unset Implicit Arguments.
Definition p230_ax_set(s:program230_configuration code_expr)(i:nat)(v:code_expr):=
 program230_config_of(fun j=>if Nat.eqb j(S i)then v else program230_field s j).
Definition p230_ax_push(s:program230_configuration code_expr)(v:code_expr):=
 p230_ax_set(p230_ax_set s 2(CEpair(program230_register s 1)(program230_register s 2)))1 v.
Definition p230_ax_binary(f:code_expr->code_expr->code_expr)(s:program230_configuration code_expr):=
 match program230_register s 2 with
 |CEpair x tail=>Some(p230_ax_set(p230_ax_set s 1(f x(program230_register s 1)))2 tail)
 |_=>None end.
Definition p230_ax_add(x y:code_expr):code_expr:=
 match x,y with CEconst 0,_=>y|_,CEconst 0=>x|_,_=>CEadd x y end.
Definition p230_ax_symbolic_step(n:nat)(s:program230_configuration code_expr):option(program230_configuration code_expr):=
 match n with
 |166=>Some(p230_ax_push s(program230_register s 4))
 |121=>Some(p230_ax_push s(program230_register s 5))
 |168=>Some(p230_ax_push s(program230_register s 3))
 |171=>Some(p230_ax_push s(CEconst 0))
 |177=>Some(p230_ax_push s(CEconst 1))
 |119=>p230_ax_binary E_wim s
 |181=>p230_ax_binary E_wel s
 |180=>p230_ax_binary E_wal s
 |182=>p230_ax_binary E_weq s
 |178=>p230_ax_binary E_wa s
 |183=>p230_ax_binary E_wex s
 |218=>Some(p230_ax_set s 1(E_wn(program230_register s 1)))
 |176=>Some(p230_ax_set(p230_ax_set s 5(CEvar 2))8(CEvar 9))
 |158=>Some(p230_ax_set(p230_ax_set s 6(CEvar 4))8(CEvar 10))
 |208=>Some(p230_ax_set(p230_ax_set s 1(p230_ax_add(program230_register s 1)(program230_register s 6)))6(CEconst 0))
 |_=>None end.
Fixpoint p230_ax_symbolic_execute(ids:list nat)(s:program230_configuration code_expr):option(program230_configuration code_expr):=
 match ids with []=>Some s|n::tail=>match p230_ax_symbolic_step n s with None=>None|Some s'=>p230_ax_symbolic_execute tail s' end end.
Definition p230_ax_symbolic_initial:=mkProgram230Configuration code_expr(CEconst 0)
 (CEvar 7)(CEvar 5)(CEvar 6)(CEvar 3)(CEvar 0)(CEvar 1)(CEconst 0)(CEconst 0)(CEvar 8).
Definition p230_ax_symbolic_final:=mkProgram230Configuration code_expr(CEconst 0)
 (CEvar 7)(E_bundle(CEvar 0)(CEvar 2)(CEvar 3))
 (E_ax_stack(CEvar 0)(CEvar 1)(CEvar 2)(CEvar 3)(CEvar 4)(CEvar 5)(CEvar 6))
 (CEvar 3)(CEvar 0)(CEvar 2)(CEconst 0)(CEconst 0)(CEvar 10).
Theorem p230_ax_symbolic_normalization:
 p230_ax_symbolic_execute p230_ax_pre_gate_ids p230_ax_symbolic_initial=Some p230_ax_symbolic_final.
Proof. vm_compute;reflexivity. Qed.
Print Assumptions p230_ax_symbolic_normalization.
