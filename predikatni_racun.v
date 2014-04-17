(* Osnovne vaje iz logike 1. reda. *)

(* Uporabimo knižnico, ki ima taktiko omega. Ta zna delati z naravnimi števili,
   če nastopajo samo linearne funkcije. *)
Require Import Omega.

(* Tip naravnih števil je nat. Ima element 0, operacijo naslednik S in običjane
   aritmetične operacije. *)

Theorem vaja_1:
  forall n : nat, exists m : nat, n < m.
Proof.
  intro n.
  exists (S n). (* naslednik od n *)
  omega.
Qed.

Theorem vaja_2 (n : nat): exists m : nat, n < m.
Proof.
  exists (1 + n).
  omega.
Qed.

Theorem vaja_4 (n m : nat): 2 * n + m + 1 = m + n + 1 + n.
Proof.
  omega.
Qed.

Theorem vaja_5 (n : nat): (exists m : nat, n = 2 * m) \/ (exists m : nat, n = 1 + 2 * m).
Proof.
  induction n.
  - left.
    exists 0 ; auto.
  - destruct IHn.
    + right.
      destruct H as [k G].
      exists k.
      omega.
    + left.
      destruct H as [k G].
      exists (k + 1).
      omega.
Qed.

Theorem vaja_6: forall n, exists m, n = 3 * m \/ n = 3 * m + 1 \/ n = 3 * m + 2.
Proof.
  (* naredimo na vajah *)
  admit.
Qed.

(* Predpostavimo, da imamo množici A in B. *)
Parameter A B : Set.

(* Predpostavimo, da imamo predikat P na A in  Q na B. *)
Parameter P : A -> Prop.
Parameter Q : B -> Prop.

Theorem vaja_7:
  forall y : B, (forall x : A , P x /\ Q y) -> (forall z : A, P z).
Proof.
  intros y H z.
  apply H.
Qed.

(* Predpostavimo relacijo R med A in B. *)
Parameter R : A -> B -> Prop.

Theorem vaja_8:
  (exists x : A, forall y : B, R x y) -> (forall y : B, exists x : A, R x y).
Proof.
  (* naredimo na vajah *)
  admit.
Qed.

Theorem vaja_9:
  ~ (exists x : A, P x) <-> forall x : A, ~ P x.
Proof.
  (* naredimo na vajah *)
  admit.
Qed.

(* Zakon o izključeni tretji možnosti. 
   Tu smo ga samo definirali, nismo ga predpostavili! *)
Definition lem := forall P : Prop, P \/ ~ P.

(* Zakon o dvojni negaciji. *)
Definition dn := forall P : Prop, ~ ~ P -> P.

Lemma vaja_10: lem -> dn.
Proof.
  (* naredimo na vajah *)
  admit.
Qed.

Lemma vaja_11: dn -> lem.
Proof.
  unfold dn, lem.
  intros D Q.
  apply D.
  intro G.
  absurd Q.
  - intro.
    apply G.
    left ; assumption.
  - apply D.
    intro L.
    apply G.
    right ; assumption.
Qed.
  
Theorem vaja_12:
  (exists x : A, P x) -> ~ forall x : A, ~ P x.
Proof.
  (* naredimo na vajah *)
  admit.
Qed.

Theorem vaja_13:
  dn -> ~ (forall x : A, ~ P x) -> exists x : A, P x.
Proof.
  intros D H.
  apply D.
  intro G.
  absurd (forall x : A, ~ P x).
  - assumption.
  - intros y K.
    absurd (exists z : A, P z).
    + assumption.
    + exists y.
      assumption.
Qed.
