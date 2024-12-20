/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.Tropical.Basic
import Mathlib.RingTheory.Polynomial.Basic
import ZKLib.Data.Math.Operations
import Init.Data.Array.Lemmas

/-!
  # Univariate Polynomials with Efficient Operations

  Note: this file was originally taken from Bolton Bailey, but has been heavily modified to fit our
  needs.
-/

section Polynomial

/-- A type analogous to `Polynomial` that supports computable operations. This polynomial is
  represented internally as an Array of coefficients.

For example the Array `#[1,2,3]` represents the polynomial `1 + 2x + 3x^2`. Two arrays may represent
the same polynomial via zero-padding, for example `#[1,2,3] = #[1,2,3,0,0,0,...]`.
 -/
structure UniPoly (R : Type _) [Semiring R] where
  mk::
  coeffs : Array R
  -- h : coeffs last is non zero
deriving Inhabited, DecidableEq, Repr

namespace UniPoly

variable {R : Type _} [Semiring R]

/-- Another way to access `coeffs` -/
def toArray (p : UniPoly R) : Array R := p.coeffs

@[simp]
def toArray_def (p : Array R) :
  (⟨p⟩ : UniPoly R).toArray = p := by rfl

/-- The size of the underlying array. This may not correspond to the degree of the corresponding
  polynomial if the array has leading zeroes. -/
def size (p : UniPoly R) : Nat := p.coeffs.size

@[simp] theorem size_eq_size (p : UniPoly R) : p.size = p.coeffs.size := rfl

/-- The constant polynomial `C r`. -/
def C (r : R) : UniPoly R := ⟨#[r]⟩

@[simp]
lemma C_def {r : R} :
  ⟨#[r]⟩ = C r := by rfl

@[simp]
lemma coeffs_of_C {r : R} :
  (C r).coeffs = #[r] := by rfl

@[simp]
lemma toArray_of_C {r : R} :
  (C r).toArray = #[r] := by rfl

/-- The variable `X`. -/
def X : UniPoly R := ⟨#[0, 1]⟩

section Operations

variable {S : Type*}

-- p(x) = a_0 + a_1 x + a_2 x^2 + ... + a_n x^n

-- eval₂ f x p = f(a_0) + f(a_1) x + f(a_2) x^2 + ... + f(a_n) x^n

/-- Evaluates a `UniPoly` at a given value, using a ring homomorphism `f: R →+* S`. -/
def eval₂ [Semiring S] (f : R →+* S) (x : S) (p : UniPoly R) : S :=
  p.coeffs.zipWithIndex.foldl (fun acc ⟨a, i⟩ => acc + f a * x ^ i) 0

/-- Evaluates a `UniPoly` at a given value. -/
def eval (x : R) (p : UniPoly R) : R :=
  p.eval₂ (RingHom.id R) x

/-- Addition of two `UniPoly`s. Defined as the pointwise sum of the underlying coefficient arrays
  (properly padded with zeroes). -/
def add (p q : UniPoly R) : UniPoly R :=
  let ⟨p', q'⟩ := Array.matchSize p.coeffs q.coeffs 0
  .mk (Array.zipWith p' q' (· + ·) )

def add_aux (p q : List R) : List R :=
  match p with
  | List.nil => q
  | x :: p' =>
    match q with
    | List.nil => p
    | y :: q' => (x + y) :: (add_aux p' q')

@[simp]
lemma add_aux_nil_left {q : List R} :
  add_aux [] q = q := by rfl

@[simp]
lemma add_aux_nil_right {q : List R} :
  add_aux q [] = q := by
  cases q <;> try simp [add_aux]

@[simp]
lemma add_aux_zero_left_nil :
  add_aux [(0 : R)] [] = [0] := by rfl

@[simp]
lemma add_aux_zero_right_nil :
  add_aux [] [(0 : R)] = [0] := by rfl

@[simp]
lemma add_aux_zero_left_cons {x : R} {q : List R} :
  add_aux [0] (x :: q) = (x :: q) := by simp [add_aux]

@[simp]
lemma add_aux_zero_right_cons {x : R} {q : List R} :
  add_aux (x :: q) [0] = (x :: q) := by simp [add_aux]


@[simp]
lemma add_aux_not_nil {x y : R} {p q : List R} :
  add_aux (x :: p) (y :: q) = (x + y) :: add_aux p q := by rfl

def add_alternative (p q : UniPoly R) : UniPoly R :=
  let (p', q') := (p.toArray.toList, q.toArray.toList)
  ⟨⟨add_aux p' q'⟩⟩

lemma add_eq_add_alternative (p q : UniPoly R) :
  add p q = add_alternative p q := by
  rcases p with ⟨⟨p⟩⟩
  rcases q with ⟨⟨q⟩⟩
  revert q
  induction p with
  | nil =>
    intro q
    unfold add add_alternative add_aux
    simp [List.zipWith_toArray, mk.injEq,
      Array.mk.injEq, List.matchSize, UniPoly.toArray, Array.toList]
    induction q with
    | nil => rfl
    | cons y q ih =>
      simp [List.replicate, List.zipWith, ih]
  | cons x p ih =>
    intro q
    unfold add add_alternative add_aux
    simp only [List.zipWith_toArray, mk.injEq, Array.mk.injEq,
      List.matchSize, UniPoly.toArray, Array.toList]
    induction q with
    | nil =>
      simp [List.replicate, List.zipWith]
      rw [List.zipWith_comm_of_comm _ (by {
        intro x y
        rw [_root_.add_comm]
      })]
      clear ih
      induction p with
      | nil => rfl
      | cons y p ihh =>
        simp [List.zipWith, List.replicate, ihh]
    | cons y q ihh =>
      simp
      have h : List.zipWith (fun x1 x2 ↦ x1 + x2) (p ++ List.replicate (q.length - p.length) 0)
          (q ++ List.replicate (p.length - q.length) 0) = (add ⟨⟨p⟩⟩ ⟨⟨q⟩⟩).coeffs.toList := by
        simp [add, List.matchSize]
      rw [h, ih]
      simp [add_alternative]

@[simp]
lemma add_nil_left {p : UniPoly R} :
  add ⟨#[]⟩ p = p := by
  simp [add_eq_add_alternative, add_alternative, toArray]

@[simp]
lemma add_nil_right {p : UniPoly R} :
  add p ⟨#[]⟩ = p := by
  simp [add_eq_add_alternative, add_alternative, toArray]

@[simp]
lemma add_zero_left_nil :
  add (C 0) ⟨#[]⟩ = C 0 := by rfl

@[simp]
lemma add_zero_right_nil :
  add ⟨#[]⟩ (C 0) = C 0 := by rfl

@[simp]
lemma add_zero_zero :
  add (C (0 : R)) (C 0) = C 0 := by
  simp [add_eq_add_alternative, add_alternative]

@[simp]
lemma add_zero_left_cons {x : R} {p : List R} :
  add (C 0) ⟨⟨x :: p⟩⟩ = ⟨⟨x :: p⟩⟩  := by
  simp [add_eq_add_alternative, add_alternative, add_aux]

@[simp]
lemma add_zero_right_cons {x : R} {p : List R} :
  add ⟨⟨x :: p⟩⟩ (C 0) = ⟨⟨x :: p⟩⟩  := by
  simp [add_eq_add_alternative, add_alternative, add_aux]

@[simp]
lemma add_cons {x y : R} {p q : List R} :
  add ⟨⟨x :: p⟩⟩ ⟨⟨y :: q⟩⟩ = ⟨⟨(x + y) :: ((add ⟨⟨p⟩⟩ ⟨⟨q⟩⟩).toArray.toList)⟩⟩ := by
  simp [add_eq_add_alternative, add_alternative, add_aux]

/-- Scalar multiplication of `UniPoly` by an element of `R`. -/
def smul (r : R) (p : UniPoly R) : UniPoly R :=
  .mk (Array.map (fun a => r * a) p.coeffs)


@[simp]
lemma smul_nil {r : R} :
  smul r ⟨#[]⟩ = ⟨#[]⟩ := by rfl

def smul_aux (r : R) (p : List R) : List R :=
  p.map (fun a => r * a)

/-- Scalar multiplication of `UniPoly` by a natural number. -/
def nsmul (n : ℕ) (p : UniPoly R) : UniPoly R :=
  .mk (Array.map (fun a => n * a) p.coeffs)

/-- Scalar multiplication of `UniPoly` by an integer. -/
def zsmul [Ring R] (z : ℤ) (p : UniPoly R) : UniPoly R :=
  .mk (Array.map (fun a => z * a) p.coeffs)

/-- Negation of a `UniPoly`. -/
def neg [Ring R] (p : UniPoly R) : UniPoly R := p.smul (-1)

/-- Subtraction of two `UniPoly`s. -/
def sub [Ring R] (p q : UniPoly R) : UniPoly R := p.add q.neg

/-- Multiplication of a `UniPoly` by `X ^ i`, i.e. pre-pending `i` zeroes to the
underlying array of coefficients. -/
def mulPowX (i : Nat) (p : UniPoly R) : UniPoly R := .mk (Array.replicate i 0 ++ p.coeffs)

/-- Multiplication of a `UniPoly` by `X`, reduces to `mulPowX 1`. -/
@[reducible] def mulX (p : UniPoly R) : UniPoly R := p.mulPowX 1

/-- Multiplication of two `UniPoly`s, using the naive `O(n^2)` algorithm. -/
def mul (p q : UniPoly R) : UniPoly R :=
  p.coeffs.zipWithIndex.foldl (fun acc ⟨a, i⟩ => acc.add <| (smul a q).mulPowX i) (C 0)

#eval mul ⟨(#[] : Array ℕ)⟩ ⟨#[]⟩

def mul_aux (p q : List R) : List R :=
  match p with
  | [] => [0]
  | a₀ :: p' =>
    match q with
    | [] => List.replicate p'.length 0
    | b₀ :: q' =>
      let const_term := a₀ * b₀
      let x_term := add_aux (smul_aux a₀ p') (smul_aux b₀ q')
      let x_square_term := mul_aux p' q'
      const_term :: (add_aux x_term (0 :: x_square_term))

def mul_alternative (p q : UniPoly R) : UniPoly R :=
  let (p', q') := (p.toArray.toList, q.toArray.toList)
  add ⟨⟨mul_aux p' q'⟩⟩ (C 0)

@[simp]
lemma add_aux_empty {p : List R} :
  add_aux p [] = p := by
  cases p <;> simp [add_aux]

@[simp]
lemma add_aux_replicate_zero {p : List R} {i : ℕ} :
  add_aux p (List.replicate i 0) = List.rightpad i 0 p := by
  revert i
  induction p with
  | nil =>
    intro i
    rfl
  | cons x g ih =>
    intro i
    have h: List.rightpad i 0 (x :: g) = x :: List.rightpad (i - 1) 0 g := by
      simp_all only [
        List.rightpad,
        List.length_cons,
        List.cons_append,
        List.cons.injEq,
        List.append_cancel_left_eq,
        List.replicate_inj, or_true, and_true, true_and]
      omega
    rw [h, ←ih]
    cases i <;> simp [add_aux, List.replicate]


theorem ext {p q : UniPoly R} (h : p.coeffs = q.coeffs) : p = q := by
  cases p; cases q; simp at h; rw [h]

@[simp]
lemma foldl_coeffs_ext.{u} {α : Type u}
  {f : UniPoly R → α → UniPoly R} {init : UniPoly R} {list : List α} :
  (List.foldl f init list).coeffs.toList
    = List.foldl (fun acc x => (f ⟨⟨acc⟩⟩ x).coeffs.toList)
                 init.coeffs.toList
                 list := by
  revert init
  induction list with
  | nil =>
    intro
    rfl
  | cons x list' ih =>
    intro init
    simp [ih]

@[simp]
lemma mulPowX_0 {p : UniPoly R} :
  mulPowX 0 p = p := by
  unfold mulPowX
  apply ext
  simp [Array.replicate]

@[simp]
lemma zero_add_mulPowX_succ {n : ℕ} {p : UniPoly R} :
  (C 0).add (mulPowX (n + 1) p) = mulPowX (n + 1) p := by
  simp [mulPowX, Array.replicate, List.replicate, add_eq_add_alternative, add_alternative]

lemma mulPowX_nil {n : ℕ} :
  (mulPowX n ⟨(#[] : Array R)⟩) = ⟨Array.replicate n 0⟩ := by rfl

@[simp]
lemma mulPowX_succ {n : ℕ} {p : UniPoly R} :
  (mulPowX (n + 1) p) = ⟨⟨0 :: (mulPowX n p).coeffs.toList⟩⟩ := by
  simp [mulPowX]
  aesop

lemma foldl_ignore_first {l : List (R × ℕ)} {init : List R} {f : List R → (R × ℕ) → List R}
  (h : ∀ acc b b', b.2 = b'.2 → f acc b = f acc b'):
  l.foldl f init = (l.map Prod.snd).foldl (λ acc x ↦ f acc (Classical.arbitrary _, x)) init := by
  induction' l with hd tl ih generalizing init
  · simp
  · simp; rw [ih, h]; simp

lemma list_replicate_succ_right.{u} {X : Type u} [Zero X] {n : ℕ} :
  List.replicate n (0 : X) ++ [0] = List.replicate (n + 1) (0 : X) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ, ih]


lemma foldl_replicate {p : List R} :
  List.foldl (λ (acc : List R) (x: R × ℕ) ↦ if x.2 ≤ acc.length then acc else acc ++ List.replicate (x.2 - acc.length) 0)
  [0]
  (List.mapIdx (λ i a ↦ (a, i + 1 + 1)) p) =
  0 :: List.replicate (p.length) (0 : R) := by
  rw [foldl_ignore_first (by simp), List.mapIdx_eq_enum_map, List.map_map, Function.uncurry_def]
  simp_rw [show (Prod.snd ∘ λ p : ℕ × R ↦ (p.2, p.1 + 1 + 1)) = (λ x ↦ x + 1 +1) ∘ Prod.fst by ext; rfl]
  rw [←List.map_comp_map]
  simp_rw [Function.comp_apply, List.enum_map_fst]
  induction' p.length with n ih
  · simp
  · rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp [list_replicate_succ_right]

theorem List.foldl_congr.{u₁, u₂} {α : Type u₁} {β : Type u₂} {as bs : List α}
  (h₀ : as = bs) {f g : β → α → β} (h₁ : f = g) {a b : β} (h₂ : a = b) :
  List.foldl f a as = List.foldl g b bs := by congr

lemma add_mulPowX₁ {i : ℕ} {p : UniPoly R} (h : p.coeffs.toList.length ≥ i):
  p.add (mulPowX i { coeffs := #[] }) = p := by
  rcases p with ⟨⟨p⟩⟩
  revert i
  induction p with
  | nil =>
    intro i h
    simp at h
    rw [h]
    simp
  | cons x p' ih =>
    intro i h
    rcases i with _ | ⟨i⟩ <;> try simp [Array.replicate, toArray, List.replicate]
    simp at h
    specialize (@ih i h)
    simp [mulPowX_nil] at ih
    simp [mulPowX_nil, ih]

lemma add_mulPowX₂ {i : ℕ} {p : UniPoly R} (h : p.coeffs.toList.length < i):
  add p (mulPowX i ⟨#[]⟩)
    = ⟨⟨p.coeffs.toList ++ (List.replicate (i - p.coeffs.toList.length) 0)⟩⟩ := by
  rcases p with ⟨⟨p⟩⟩
  revert i
  induction p with
  | nil =>
    intro i h
    simp at h
    simp [mulPowX_nil]
  | cons x p' ih =>
    intro i h
    rcases i with _ | ⟨i⟩ <;> try simp
    simp at h
    specialize (@ih i h)
    simp at ih
    simp [ih]

lemma add_mulPowX {i : ℕ} {p : UniPoly R} :
  p.add (mulPowX i { coeffs := #[] }) =
    if p.coeffs.toList.length ≥ i
    then p else ⟨p.coeffs ++ Array.replicate (i - p.coeffs.toList.length) 0⟩ := by
    by_cases h : (p.coeffs.toList.length ≥ i)
    rw [add_mulPowX₁ h]
    simp [h]
    simp at h
    rw [add_mulPowX₂ h]
    aesop

lemma mul_eq_mul_alternative (p q : UniPoly R):
  mul p q = mul_alternative p q := by
  rcases p with ⟨⟨p⟩⟩
  rcases q with ⟨⟨q⟩⟩
  unfold mul mul_alternative mul_aux
  simp only [Array.size_zipWithIndex, Array.size_toArray, Array.zipWithIndex, toArray, add_alternative]
  revert q
  induction p with
  | nil =>
    simp
  | cons a₀ p' ih =>
    intro q
    simp [Array.toList]
    apply ext
    have hArrayExt : ∀ (x y : Array R), x.toList = y.toList → x = y := by
      rintro ⟨x⟩ ⟨y⟩ h
      simp at h
      rw [h]
    apply hArrayExt
    simp
    rcases q with _ | ⟨y, q'⟩
    simp
    rcases p' with _ | ⟨z, p''⟩ <;> try simp [List.replicate]
    have hh : ((⟨⟨List.replicate (p''.length + 1) 0⟩⟩ : UniPoly R).add (C (0 : R)))
        = { coeffs := { toList := List.replicate (p''.length + 1) 0 } } := by
        simp [List.replicate]
    rw [List.foldl_congr (by rfl) (by {
      apply funext₂
      intro a b
      simp [add_mulPowX]
      trans (if b.2 ≤ a.length then a
      else a ++ List.replicate (b.2 - a.length) 0)
      by_cases b.2 ≤ a.length <;> try aesop
      rfl
    }) (by rfl)]
    rw [foldl_replicate]
    simp
    simp [C, smul, mulPowX]
    clear ih
    induction p' with
    | nil => rfl
    | cons x p'' ih =>
      simp [List.replicate]
      simp [List.replicate] at ih
      rw [←ih]

    rw [List.foldl_congr (by rfl) (by {
        trans (fun acc x ↦ acc.add_alternative (mulPowX x.2 (smul x.1 { coeffs := { toList := q } }))) <;> try rfl
        apply funext₂
        rintro x ⟨y, i⟩
        simp [add_eq_add_alternative]
      }) (by rfl) (by rfl) (by rfl)]
    apply Array.toList
    simp
    rw [foldl_coeffs_ext]
    induction q with
    | nil =>
      simp [add_alternative, mulPowX, add_aux, toArray, Array.toList, C, smul, List.replicate]
      specialize (ih [])
      simp [C, Array.toList] at ih
      cases p' <;> try simp
      simp [List.replicate] at ih
      rw [←ih]
      simp
      clear ih
      induction p' with
      | nil => rfl
      | cons x p'' ih =>
        simp [add_aux]


      simp [C, add, Array.toList, List.zipWith, List.matchSize]



    | cons b₀ q' ihq => sorry



/-- Exponentiation of a `UniPoly` by a natural number `n` via repeated multiplication. -/
def pow (p : UniPoly R) (n : Nat) : UniPoly R := (mul p)^[n] (C 1)

-- TODO: define repeated squaring version of `pow`

instance : Zero (UniPoly R) := ⟨UniPoly.mk #[]⟩
instance : One (UniPoly R) := ⟨UniPoly.C 1⟩
instance : Add (UniPoly R) := ⟨UniPoly.add⟩
instance : SMul R (UniPoly R) := ⟨UniPoly.smul⟩
instance : SMul ℕ (UniPoly R) := ⟨UniPoly.nsmul⟩
instance [Ring R] : SMul ℤ (UniPoly R) := ⟨UniPoly.zsmul⟩
instance [Ring R] : Neg (UniPoly R) := ⟨UniPoly.neg⟩
instance [Ring R] : Sub (UniPoly R) := ⟨UniPoly.sub⟩
instance : Mul (UniPoly R) := ⟨UniPoly.mul⟩
instance : Pow (UniPoly R) Nat := ⟨UniPoly.pow⟩
instance : NatCast (UniPoly R) := ⟨fun n => UniPoly.C (n : R)⟩
instance [Ring R] : IntCast (UniPoly R) := ⟨fun n => UniPoly.C (n : R)⟩

/-- Convert a `UniPoly` to a `Polynomial`. -/
noncomputable def toPoly (p : UniPoly R) : Polynomial R :=
  p.eval₂ Polynomial.C Polynomial.X

/-- Return a bound on the degree of a `UniPoly` as the size of the underlying array
(and `⊥` if the array is empty). -/
def degreeBound (p : UniPoly R) : WithBot Nat :=
  match p.coeffs.size with
  | 0 => ⊥
  | .succ n => n

/-- Convert `degreeBound` to a natural number by sending `⊥` to `0`. -/
def natDegreeBound (p : UniPoly R) : Nat :=
  (degreeBound p).getD 0

/-- Remove leading zeroes from a `UniPoly`. Requires `BEq` to check if the coefficients are zero. -/
def trim [BEq R] (p : UniPoly R) : UniPoly R := ⟨p.coeffs.popWhile (fun a => a == 0)⟩

/-- Return the degree of a `UniPoly` as size of the underlying trimmed array. -/
def degree [BEq R] (p : UniPoly R) : Nat := p.trim.size

/-- Return the leading coefficient of a `UniPoly` as the last coefficient of the trimmed array,
or `0` if the trimmed array is empty. -/
def leadingCoeff [BEq R] (p : UniPoly R) : R := p.trim.coeffs.getLastD 0

/-- Check if a `UniPoly` is monic, i.e. its leading coefficient is 1. -/
def monic [BEq R] (p : UniPoly R) : Bool := p.leadingCoeff == 1

-- TODO: remove dependence on `BEq` for division and modulus

/-- Division and modulus of `p : UniPoly R` by a monic `q : UniPoly R`. -/
def divModByMonicAux [BEq R] [Field R] (p : UniPoly R) (q : UniPoly R) :
    UniPoly R × UniPoly R :=
  go (p.size - q.size) p q
where
  go : Nat → UniPoly R → UniPoly R → UniPoly R × UniPoly R
  | 0, p, _ => ⟨0, p⟩
  | n+1, p, q =>
      let k := p.coeffs.size - q.coeffs.size -- k should equal n, this is technically unneeded
      let q' := C p.leadingCoeff * (q * X.pow k)
      let p' := (p - q').trim
      let (e, f) := go n p' q
      -- p' = q * e + f
      -- Thus p = p' + q' = q * e + f + p.leadingCoeff * q * X^n
      -- = q * (e + p.leadingCoeff * X^n) + f
      ⟨e + C p.leadingCoeff * X^k, f⟩

/-- Division of `p : UniPoly R` by a monic `q : UniPoly R`. -/
def divByMonic [BEq R] [Field R] (p : UniPoly R) (q : UniPoly R) :
    UniPoly R :=
  (divModByMonicAux p q).1

/-- Modulus of `p : UniPoly R` by a monic `q : UniPoly R`. -/
def modByMonic [BEq R] [Field R] (p : UniPoly R) (q : UniPoly R) :
    UniPoly R :=
  (divModByMonicAux p q).2

/-- Division of two `UniPoly`s. -/
def div [BEq R] [Field R] (p q : UniPoly R) : UniPoly R :=
  (C (q.leadingCoeff)⁻¹ • p).divByMonic (C (q.leadingCoeff)⁻¹ * q)

/-- Modulus of two `UniPoly`s. -/
def mod [BEq R] [Field R] (p q : UniPoly R) : UniPoly R :=
  (C (q.leadingCoeff)⁻¹ • p).modByMonic (C (q.leadingCoeff)⁻¹ * q)

instance [BEq R] [Field R] : Div (UniPoly R) := ⟨UniPoly.div⟩
instance [BEq R] [Field R] : Mod (UniPoly R) := ⟨UniPoly.mod⟩

/-- Pseudo-division of a `UniPoly` by `X`, which shifts all non-constant coefficients
to the left by one. -/
def divX (p : UniPoly R) : UniPoly R := ⟨p.coeffs.extract 1 p.size⟩

@[simp] theorem zero_def : (0 : UniPoly R) = ⟨#[]⟩ := rfl

theorem add_comm (p q : UniPoly R) : p + q = q + p := by
  simp only [instHAdd, Add.add, add, List.zipWith_toArray, mk.injEq, Array.mk.injEq]
  exact List.zipWith_comm_of_comm _ (fun x y ↦ by change x + y = y + x; rw [_root_.add_comm]) _ _

theorem add_mul_distr (p q r : UniPoly R) :
  p * (q + r) = p * q + p * r := by
  simp only [instHAdd, Add.add, add, instHMul, Mul.mul, mul, List.zipWith_toArray]
  simp


@[simp] theorem zero_add (p : UniPoly R) : 0 + p = p := by
  simp [instHAdd, instAdd, add, List.matchSize]
  refine UniPoly.ext (Array.ext' ?_)
  simp [Array.toList_zipWith, List.zipWith]
  sorry

@[simp] theorem add_assoc (p q r : UniPoly R) : p + q + r = p + (q + r) := by
  simp [instHAdd, instAdd, add, List.matchSize]
  -- refine Array.ext' ?_
  -- simp [Array.toList_zipWith]
  sorry

-- TODO: define `SemiRing` structure on `UniPoly`
-- instance : AddCommMonoid (UniPoly R) := {
--   add_assoc := fun p q r => by simp [instHAdd, instAdd, add]
--   zero_add := sorry
--   add_zero := sorry
--   add_comm := sorry
--   nsmul := sorry
-- }



end Operations


section Equiv

/-- An equivalence relation `equiv` on `UniPoly`s where `p ~ q` iff one is a
zero-padding of the other. -/
def equiv (p q : UniPoly R) : Prop :=
  match p.coeffs.matchSize q.coeffs 0 with
  | (p', q') => p' = q'

/-- Reflexivity of the equivalence relation. -/
@[simp] theorem equiv_refl (p : UniPoly R) : equiv p p :=
  by simp [equiv, List.matchSize]

/-- Symmetry of the equivalence relation. -/
@[simp] theorem equiv_symm {p q : UniPoly R} : equiv p q → equiv q p :=
  fun h => by simp [equiv] at *; exact Eq.symm h

open List in
/-- Transitivity of the equivalence relation. -/
@[simp] theorem equiv_trans {p q r : UniPoly R} : equiv p q → equiv q r → equiv p r :=
  fun hpq hqr => by
    simp_all [equiv, Array.matchSize]
    have hpq' := (List.matchSize_eq_iff_forall_eq p.coeffs.toList q.coeffs.toList 0).mp hpq
    have hqr' := (List.matchSize_eq_iff_forall_eq q.coeffs.toList r.coeffs.toList 0).mp hqr
    have hpr' : ∀ (i : Nat), p.coeffs.toList.getD i 0 = r.coeffs.toList.getD i 0 :=
      fun i => Eq.trans (hpq' i) (hqr' i)
    exact (List.matchSize_eq_iff_forall_eq p.coeffs.toList r.coeffs.toList 0).mpr hpr'

/-- The `UniPoly.equiv` is indeed an equivalence relation. -/
instance instEquivalenceEquiv : Equivalence (equiv (R := R)) where
  refl := equiv_refl
  symm := equiv_symm
  trans := equiv_trans

/-- The `Setoid` instance for `UniPoly R` induced by `UniPoly.equiv`. -/
instance instSetoidUniPoly: Setoid (UniPoly R) where
  r := equiv
  iseqv := instEquivalenceEquiv

/-- The quotient of `UniPoly R` by `UniPoly.equiv`. This will be shown to be equivalent to
  `Polynomial R`. -/
def QuotientUniPoly := Quotient (@instSetoidUniPoly R _)

-- TODO: show that operations on `UniPoly` descend to `QuotientUniPoly`



end Equiv

end UniPoly

-- unique polynomial of degree n that has nodes at ω^i for i = 0, 1, ..., n-1
def Lagrange.nodal' {F : Type} [Semiring F] (n : ℕ) (ω : F) : UniPoly F :=
  .mk (Array.range n |>.map (fun i => ω^i))

/--
This function produces the polynomial which is of degree n and is equal to r i at ω^i for i = 0, 1,
..., n-1.
-/
def Lagrange.interpolate' {F : Type} [Semiring F] (n : ℕ) (ω : F) (r : Fin n → F) : UniPoly F :=
  -- .mk (Array.finRange n |>.map (fun i => r i))
  sorry

section Tropical
/-- This section courtesy of Junyan Xu -/

instance : LinearOrderedAddCommMonoidWithTop (OrderDual (WithBot ℕ)) where
  __ : LinearOrderedAddCommMonoid (OrderDual (WithBot ℕ)) := inferInstance
  __ : Top (OrderDual (WithBot ℕ)) := inferInstance
  le_top _ := bot_le (α := WithBot ℕ)
  top_add' x := WithBot.bot_add x


noncomputable instance (R) [Semiring R] : Semiring (Polynomial R × Tropical (OrderDual (WithBot ℕ)))
  := inferInstance

noncomputable instance (R) [CommSemiring R] : CommSemiring
    (Polynomial R × Tropical (OrderDual (WithBot ℕ))) := inferInstance


def TropicallyBoundPoly (R) [Semiring R] : Subsemiring
    (Polynomial R × Tropical (OrderDual (WithBot ℕ))) where
  carrier := {p | p.1.degree ≤ OrderDual.ofDual p.2.untrop}
  mul_mem' {p q} hp hq := (p.1.degree_mul_le q.1).trans (add_le_add hp hq)
  one_mem' := Polynomial.degree_one_le
  add_mem' {p q} hp hq := (p.1.degree_add_le q.1).trans (max_le_max hp hq)
  zero_mem' := Polynomial.degree_zero.le


noncomputable def UniPoly.toTropicallyBoundPolynomial {R : Type} [Semiring R] (p : UniPoly R) :
    Polynomial R × Tropical (OrderDual (WithBot ℕ)) :=
  (UniPoly.toPoly p, Tropical.trop (OrderDual.toDual (UniPoly.degreeBound p)))

def degBound (b: WithBot ℕ) : ℕ := match b with
  | ⊥ => 0
  | some n => n + 1

def TropicallyBoundPolynomial.toUniPoly {R : Type} [Semiring R]
    (p : Polynomial R × Tropical (OrderDual (WithBot ℕ))) : UniPoly R :=
  match p with
  | (p, n) => UniPoly.mk (Array.range (degBound n.untrop) |>.map (fun i => p.coeff i))

noncomputable def Equiv.UniPoly.TropicallyBoundPolynomial {R : Type} [Semiring R] :
    UniPoly R ≃+* Polynomial R × Tropical (OrderDual (WithBot ℕ)) where
      toFun := UniPoly.toTropicallyBoundPolynomial
      invFun := TropicallyBoundPolynomial.toUniPoly
      left_inv := by sorry
      right_inv := by sorry
      map_mul' := by sorry
      map_add' := by sorry

end Tropical

def xMinusA {R: Type} [Ring R] (a : R) : UniPoly R
  := ⟨#[-a, 1]⟩

@[simp]
lemma x_minus_a_on_b_eq_b_minus_a {R: Type} [Ring R] (a b : R):
  (xMinusA a).eval b = b - a := by
  unfold UniPoly.eval UniPoly.eval₂ xMinusA Array.zipWithIndex
  simp
  rw [add_comm, Mathlib.Tactic.RingNF.add_neg]

@[simp]
lemma x_minus_a_on_a_eq_zero {R: Type} [Ring R] (a : R) :
  (xMinusA a).eval a = 0 := by simp

lemma x_minus_a_eq_zero_implies_x_eq_a {R: Type} [Ring R] (a b : R)
  (h: (xMinusA a).eval b = 0): b = a := by
    simp at h
    have hh : a = a + (b - a) := by simp only [h, add_zero]
    rw [hh]
    have hh : a + (b - a) = (b - a) + a := by simp only [add_comm]
    rw [hh]
    simp only [sub_add_cancel]

def evalsToPoly {R: Type} [Ring R] (evals : List R) : UniPoly R
  := match evals with
  | [] => ⟨#[1]⟩
  | x :: g => UniPoly.mul (xMinusA x) (evalsToPoly g)

def linearize {R: Type} [Semiring R] (f : UniPoly R) : (R × UniPoly R) :=
  (f.coeffs[0]?.getD 0, ⟨f.coeffs.eraseIdx! 0⟩)

@[simp]
lemma const_poly_coeffs {R: Type} [Semiring R] {x : R}:
  (UniPoly.C x).coeffs = #[x] := by rfl

@[simp]
lemma mulPowX1_coeffs {R: Type} [Semiring R] {f : UniPoly R} :
  (UniPoly.mulPowX 1 f).coeffs = #[0] ++ f.coeffs := by rfl

@[simp]
lemma const_add_mulPowX1_aux {R: Type} [Semiring R] {f : UniPoly R} {x : R} :
  ((UniPoly.C x).add (UniPoly.mulPowX 1 f)).coeffs = #[x] ++ f.coeffs := by
  unfold UniPoly.C UniPoly.add
  simp [List.matchSize]
  rcases f with ⟨⟨f⟩⟩
  simp
  induction f with
  | nil => rfl
  | cons x tail ih =>
    simp
    unfold List.zipWith List.replicate
    simp
    rw [ih]

@[simp]
lemma const_add_mulPowX1 {R: Type} [Semiring R] {f : UniPoly R} {x : R} :
  ((UniPoly.C x) + (UniPoly.mulPowX 1 f)).coeffs = #[x] ++ f.coeffs := by
  change ((UniPoly.C x).add (UniPoly.mulPowX 1 f)).coeffs = #[x] ++ f.coeffs
  simp

lemma polynomial_ext {R: Type} [Semiring R] {f g : UniPoly R} {x : R} (h : f.coeffs = g.coeffs) :
  UniPoly.eval x f = UniPoly.eval x g := by
  rcases f with ⟨⟨f⟩⟩
  rcases g with ⟨⟨g⟩⟩
  simp at h
  rw [h]

lemma linearization_spec {R: Type} [Semiring R] (f : UniPoly R) (x : R):
  UniPoly.eval x f = let (a₀, a₁) := linearize f
    UniPoly.eval x (UniPoly.C a₀ + UniPoly.mulPowX 1 a₁) := by
    rcases f with ⟨⟨f⟩⟩
    simp [linearize]
    rcases f
    unfold UniPoly.eval UniPoly.eval₂
    simp
    unfold Array.zipWithIndex Array.eraseIdx!
    simp
    rw [Array.foldl_congr (by {
      change Array.mapIdx (fun i a ↦ (a, i)) (#[0] ++ default) = #[(0,0)]
      rfl
    }) (by rfl) (by rfl) (by rfl) (by {
      simp [default]
      change 1 + #[].size = 1
      rfl
    })]
    simp
    apply polynomial_ext
    simp [Array.eraseIdx!]

lemma

theorem eval_mul_eq_muls_eval {R: Type} [Semiring R] {f g: List R} {x : R} :
  UniPoly.eval x (UniPoly.mul ⟨f.toArray⟩ ⟨g.toArray⟩)
  = (UniPoly.eval x ⟨f.toArray⟩) * (UniPoly.eval x ⟨g.toArray⟩) := by
  revert g
  induction f with
  | nil =>
    intro g
    unfold UniPoly.eval UniPoly.eval₂ UniPoly.mul Array.zipWithIndex
    simp
    have h: (Array.mapIdx (fun i a ↦ (a, i)) (@UniPoly.C R _ 0).coeffs) = #[(0, 0)] := by rfl
    rw [Array.foldl_congr (by rw [h]) (by rfl) (by rfl) (by rfl) (by {
      have h: (UniPoly.C 0).coeffs.size
        = (Array.mapIdx (fun i a ↦ (a, i)) (UniPoly.C 0).coeffs).size := by rfl
      exact h
    })]
    have h: (UniPoly.C 0).coeffs = #[0] := by rfl
    rw [h]
    simp
  | cons a f ih =>
    intro g
    unfold UniPoly.eval UniPoly.eval₂ UniPoly.mul Array.zipWithIndex
    simp


lemma evals_to_poly_eq_zero_iff_x_is_a_root {R: Type} [Ring R] [IsDomain R] {evals : List R}
  {x : R}:
  (evalsToPoly evals).eval x = 0 ↔ x ∈ evals := by
  revert x
  induction evals with
  | nil =>
    simp [evalsToPoly, UniPoly.eval, UniPoly.eval₂, Array.zipWithIndex]
  | cons a g ih => {
    intro x
    simp [evalsToPoly]


  }

end Polynomial
