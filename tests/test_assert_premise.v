Require Import Arith.
Require Import LibHyps.LibHyps.
Require Import Ltac2.Ltac2.
Local Set Default Proof Mode "Classic".

Definition eq_one (i:nat) := i = 1.

(* Default configuration: variables are quantified unless not
   appearing in the type of the created hypothesis *)
Ltac2 Set on_cited_vars := Evarize.
Ltac2 Set dont_quantif_unused := true.

Lemma test_espec_namings_premis: forall n:nat, (eq_one n -> eq_one 1 -> False) -> True.
Proof.
  intros n h_eqone.
  assert premise 1 of Nat.quadmul_le_squareadd with a as h.
  { apply le_n. }
  Undo 4.
  assert premise 1 of Nat.quadmul_le_squareadd with a as hh (*: h*).
  { apply le_n. }
  Undo 4.
  assert premise 1 of min_l with n,m as hhh.
  { apply (le_n O). }
  Undo 4.
  assert premise 1 of min_l as hhh.
  { admit. }
  Undo 4.
  
  especialize h_eqone at 2 as h1 (*: h2 *).
  { reflexivity. }
  (* unfold eq_one in h2. *)
  (* match type of h2 with 1 = 1 => idtac | _ => fail end. *)
  match type of h1 with eq_one n -> False => idtac | _ => fail end.
  exact I.
Qed.

(* Testing the four variants of these config. *)

Ltac2 Set on_cited_vars := Evarize.
Ltac2 Set dont_quantif_unused := false.

Goal (forall n p m:nat, n<=m -> n<m -> n=p -> False) -> True.
  intros h. 
  assert premise 1 -> 2 of h with n,m as hh.
  match goal with
  | |- (nat -> ?n <= ?m -> ?n < ?m) => idtac
  end.
  2:match type of hh with (nat -> ?n <= ?m -> ?n < ?m) => idtac end.
  Undo 3.
  assert premise 2 of h with n as hh.
  match goal with
  | |-  nat -> forall m : nat, ?n < m =>  idtac
  end.
  Undo 2.
  assert premise 2 of h as hh.
  match goal with
  | |- forall n : nat, nat -> forall m : nat, n < m =>  idtac
  end.
  Undo 2.
  assert premise 1 -> 2 -> 3 of h as hh.
  match goal with
  | |- forall n p m : nat, n <= m -> n < m -> n = p => idtac
  end.
  Undo 2.
  assert premise 1 -> 2 of h with n,m.
  match goal with
  | |- (nat -> ?n <= ?m -> ?n < ?m) => idtac
  end.
  2:match type of H with (nat -> ?n <= ?m -> ?n < ?m) => idtac end.
  Undo 3.
  assert premise 2 of h with n.
  match goal with
  | |-  nat -> forall m : nat, ?n < m =>  idtac
  end.
  Undo 2.
  assert premise 2 of h.
  match goal with
  | |- forall n : nat, nat -> forall m : nat, n < m =>  idtac
  end.
  Undo 2.
  assert premise 1 -> 2 -> 3 of h.
  match goal with
  | |- forall n p m : nat, n <= m -> n < m -> n = p => idtac
  end.
  Undo 2.

Ltac2 Set on_cited_vars := Evarize.
Ltac2 Set dont_quantif_unused := true.

  assert premise 1 -> 2 of h with n,m as hh.
  match goal with
  | |- (?n <= ?m -> ?n < ?m) => idtac
  end.
  2:match type of hh with (?n <= ?m -> ?n < ?m) => idtac end.
  Undo 3.
  assert premise 2 of h with n as hh.
  match goal with
  | |-  forall m : nat, ?n < m =>  idtac
  end.
  Undo 2.
  assert premise 2 of h as hh.
  match goal with
  | |- forall n : nat, forall m : nat, n < m =>  idtac
  end.
  Undo 2.
  assert premise 1 -> 2 -> 3 of h as hh.
  match goal with
  | |- forall n p m : nat, n <= m -> n < m -> n = p => idtac
  end.
  Undo 2.
  assert premise 1 -> 2 of h with n,m.
  match goal with
  | |- (?n <= ?m -> ?n < ?m) => idtac
  end.
  2:match type of H with (?n <= ?m -> ?n < ?m) => idtac end.
  Undo 3.
  assert premise 2 of h with n.
  match goal with
  | |-  forall m : nat, ?n < m =>  idtac
  end.
  Undo 2.
  assert premise 2 of h.
  match goal with
  | |- forall n : nat, forall m : nat, n < m =>  idtac
  end.
  Undo 2.
  assert premise 1 -> 2 -> 3 of h.
  match goal with
  | |- forall n p m : nat, n <= m -> n < m -> n = p => idtac
  end.
  Undo 2.


Ltac2 Set on_cited_vars := Quantify.
Ltac2 Set dont_quantif_unused := false.

  assert premise 1 -> 2 of h with n,m as hh.
  match goal with
  | |- forall n m : nat, n <= m -> n < m => idtac
  end.
  2:match type of hh with (forall n m : nat, n <= m -> n < m) => idtac end.
  Undo 3.
  assert premise 2 of h with n as hh.
  match goal with
  | |-  forall n : nat, n < ?m =>  idtac
  end.
  Undo 2.
  assert premise 2 of h as hh.
  match goal with
  | |- ?n < ?m =>  idtac
  end.
  Undo 2.
  assert premise 1 -> 2 -> 3 of h as hh.
  match goal with
  | |- ?n <= ?m -> ?n < ?m -> ?n = ?p => idtac
  end.
  Undo 2.
  assert premise 1 -> 2 of h with n,m.
  match goal with
  | |- forall n m : nat, n <= m -> n < m => idtac
  end.
  2:match type of H with (forall n m : nat, n <= m -> n < m) => idtac end.
  Undo 3.
  assert premise 2 of h with n.
  match goal with
  | |- forall n : nat, n < ?m =>  idtac
  end.
  Undo 2.
  assert premise 2 of h.
  match goal with
  | |- ?n < ?m =>  idtac
  end.
  Undo 2.
  assert premise 1 -> 2 -> 3 of h.
  match goal with
  | |- ?n <= ?m -> ?n < ?m -> ?n = ?p => idtac
  end.
  Undo 2.

Ltac2 Set on_cited_vars := Quantify.
Ltac2 Set dont_quantif_unused := true. (* should not change anything, since we (don't) evar unused vars anyways. *)

  assert premise 1 -> 2 of h with n,m as hh.
  match goal with
  | |- forall n m : nat, n <= m -> n < m => idtac
  end.
  2:match type of hh with (forall n m : nat, n <= m -> n < m) => idtac end.
  Undo 3.
  assert premise 2 of h with n as hh.
  match goal with
  | |-  forall n : nat, n < ?m =>  idtac
  end.
  Undo 2.
  assert premise 2 of h as hh.
  match goal with
  | |- ?n < ?m =>  idtac
  end.
  Undo 2.
  assert premise 1 -> 2 -> 3 of h as hh.
  match goal with
  | |- ?n <= ?m -> ?n < ?m -> ?n = ?p => idtac
  end.
  Undo 2.
  assert premise 1 -> 2 of h with n,m.
  match goal with
  | |- forall n m : nat, n <= m -> n < m => idtac
  end.
  2:match type of H with (forall n m : nat, n <= m -> n < m) => idtac end.
  Undo 3.
  assert premise 2 of h with n.
  match goal with
  | |- forall n : nat, n < ?m =>  idtac
  end.
  Undo 2.
  assert premise 2 of h.
  match goal with
  | |- ?n < ?m =>  idtac
  end.
  Undo 2.
  assert premise 1 -> 2 -> 3 of h.
  match goal with
  | |- ?n <= ?m -> ?n < ?m -> ?n = ?p => idtac
  end.
  Undo 2.
Abort.
