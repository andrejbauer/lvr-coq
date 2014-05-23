(** Nastavek za urejanje z zlivanjem.
    Ostali algoritmi imajo podoben nastavek. *)

Require Import List.
Require Import ZArith.
Require Import sort. (* roba od Bauerja *)
Require Import Recdef. (* to potrbujemo za definicijo s [Function]. *)

Definition length2 (p : list Z * list Z) :=
  length (fst p) + length (snd p).

Function zlij (p : list Z * list Z) {measure length2 p} :=
  match p with
    | (nil, l2) => l2
    | (l1, nil) => l1
    | ((x :: l1') as l1, (y :: l2') as l2) =>
      if Z.leb x y then x :: zlij (l1', l2) else y :: zlij (l1, l2')
  end.
Proof.
  - intros.
    unfold length2; simpl.
    omega.
  - intros.
    unfold length2; simpl.
    omega.
Qed.

Function merge (l : list Z) {measure length l} :=
  match l with
    | nil => nil
    | (_ :: nil) => l
    | (_ :: _ :: _) =>
      let (l1, l2) := razpolovi l in
      let l1' := merge l1 in
      let l2' := merge l2 in
        zlij (l1', l2')
  end.
Proof.
  - intros. admit.
  - intros. admit.
Qed.

Theorem merge_deluje_1 : forall l : list Z, urejen (merge l).
Admitted. (* To bo naredil Tomaž. *)

Theorem merge_deluje_2 : forall l : list Z, enak l (merge l).
Admitted. (* To bo naredil Andrej. *)
