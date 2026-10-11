import Mathlib

set_option linter.style.setOption false
set_option linter.style.multiGoal false
set_option linter.style.whitespace false
set_option pp.proofs false

namespace Oset

--The proof that a set K is a subgroup of G if K is nonempty, and ab⁻¹∈K
theorem subgroup_criterion
    {G : Type} [Group G]
    (H : Set G)
    (h_nonempty : ∃ x, x ∈ H)
    (h_criterion : ∀ {a b : G}, a ∈ H → b ∈ H → a * b⁻¹ ∈ H) :
    ∃ K : Subgroup G, K = H := by
  have h_one : 1 ∈ H := by
    rcases h_nonempty with ⟨x, hx⟩
    have xx : x * x⁻¹ ∈ H := by
      apply h_criterion
      exact hx
      exact hx
    rw[← mul_inv_cancel x]
    exact xx
  have h_mem : ∀ {a}, a ∈ H → a⁻¹ ∈ H := by
    intro a ha
    have a1 : 1 * a⁻¹ ∈ H := by
      apply h_criterion
      exact h_one
      exact ha
    rw[one_mul] at a1
    exact a1
  have h_mul : ∀ {a b}, a ∈ H → b ∈ H → a * b ∈ H := by
    intro a b ah bh
    rw[← inv_inv b]
    apply h_criterion
    exact ah
    apply h_mem
    exact bh
  let K : Subgroup G := {
    carrier := H
    mul_mem' := h_mul
    one_mem' := h_one
    inv_mem' := h_mem
  }
  use K
  rfl

structure bijection (G H : Type) where
  f : G → H
  inj : ∀ a : G, ∀ b : G, (f (a) = f (b) → a = b)
  sur : ∀ a : H, ∃ b : G, (f (b) = a)
structure homomorphism (G H : Type) [Group G] [Group H] where
  f : G → H
  oneMem : f (1 : G) = (1 : H)
  hom : ∀ a : G, ∀ b : G, (f (a*b) = f (a) * f (b))
structure isomorphism (G H : Type) [Group G] [Group H] where
  f : G → H
  inj : ∀ a : G, ∀ b : G, (f (a) = f (b) → a = b)
  sur : ∀ a : H, ∃ b : G, (f (b) = a)
  hom : ∀ a : G, ∀ b : G, (f (a*b) = f (a) * f (b))

def fiber {G H : Type} [Group G] [Group H] (φ : homomorphism G H) (h : H) : (Set G) :=
  {x | φ.f x = h}
def kern {G H : Type} [Group G] [Group H] (φ : homomorphism G H) : (Set G) :=
  fiber φ 1
def kerIm {G H : Type} [Group G] [Group H] (φ : homomorphism G H) : (Set H) :=
  {y | ∃ x : G, φ.f (x) = y}
def leftCoset {G : Type} [Group G] (K : Subgroup G) (g : G) : Set G :=
  {x | ∃ k ∈ K, g * k = x}
def rightCoset {G : Type} [Group G] (K : Subgroup G) (g : G) : Set G :=
  {x | ∃ k ∈ K, k * g = x}
def centralizer {G : Type} [Group G] (A : Set G) : Set G :=
  {g | ∀ a ∈ A, g * a * g⁻¹ = a}
def centralSubgroup {G : Type} [Group G] (A : Set G) : Subgroup G := by
  refine {
    carrier := centralizer A
    mul_mem' := by
      intro a b aInCA bInCA x xInA
      rw[mul_inv_rev]
      nth_rewrite 2 [← aInCA x xInA, ← bInCA x xInA]
      simp only [mul_assoc]
    one_mem' := by
      intro a ha
      symm
      rw[one_mul, eq_mul_inv_iff_mul_eq, mul_one]
    inv_mem' := by
      intro x xInCA y yInA
      symm
      rw[eq_mul_inv_iff_mul_eq, eq_inv_mul_iff_mul_eq,← mul_assoc]
      apply xInCA y
      assumption
  }
def conjugateSet {G : Type} [Group G] (K : Set G) (g : G) : Set G :=
  {x | ∃ k ∈ K, g * k * g⁻¹ = x}
def normalizer {G : Type} [Group G] (A : Set G) : Set G :=
  {g | conjugateSet A g = A}
def normalizerSubgroup {G : Type} [Group G] (A : Set G) : Subgroup G := by
  refine {
    carrier := normalizer A
    mul_mem' := by
      intro a b aInNorm bInNorm
      change conjugateSet A a = A at aInNorm
      change conjugateSet A b = A at bInNorm
      rw[Set.ext_iff] at aInNorm bInNorm
      change  ∀ (x : G), (∃ k ∈ A, a * k * a⁻¹ = x) ↔ x ∈ A at aInNorm
      change  ∀ (x : G), (∃ k ∈ A, b * k * b⁻¹ = x) ↔ x ∈ A at bInNorm
      ext z
      constructor
      · intro zInConj
        rcases zInConj with ⟨x,⟨xInA, xEqz⟩⟩
        rw[← aInNorm]
        use (a⁻¹ * z * a)
        constructor
        · rw [mul_inv_rev, Eq.comm, ← mul_assoc, eq_mul_inv_iff_mul_eq,Eq.comm,mul_assoc] at xEqz
          nth_rewrite 1 [mul_assoc, ←  eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc] at xEqz
          rw[← xEqz,← bInNorm (b * x * b⁻¹)]
          use x
        · simp [mul_inv_cancel, mul_assoc]
      · intro zInA
        change ∃ k ∈ A, (a*b) * k * (a*b)⁻¹ = z
        specialize aInNorm z
        rw[← aInNorm] at zInA
        rcases zInA with ⟨x,⟨xInA,xEqz⟩⟩
        specialize bInNorm (a⁻¹*z*a)
        rw[Eq.comm, eq_mul_inv_iff_mul_eq, Eq.comm,← eq_inv_mul_iff_mul_eq,← mul_assoc] at xEqz
        rw[xEqz,← bInNorm] at xInA
        rcases xInA with ⟨y, ⟨yInA, yEqz⟩⟩
        rw[Eq.comm, eq_mul_inv_iff_mul_eq, Eq.comm,← eq_inv_mul_iff_mul_eq,← mul_assoc] at yEqz
        rw[yEqz] at yInA
        simp only [← mul_assoc] at yInA
        use b⁻¹ * a⁻¹ * z * a * b
        constructor
        · assumption
        · simp [← mul_assoc]
    one_mem' := by
      change conjugateSet A 1 = A
      ext z
      change (∃ k ∈ A, (1 : G) * k * (1 : G)⁻¹ = z) ↔ z ∈ A
      constructor
      · intro x
        rcases x with ⟨w,⟨wInA, wEqz⟩⟩
        simp only [mul_one,one_mul,inv_one] at wEqz
        rwa[← wEqz]
      · intro zInA
        use z
        constructor
        · assumption
        · simp
    inv_mem' := by
      intro x xInNorm
      change conjugateSet A x⁻¹ = A
      change conjugateSet A x = A at xInNorm
      rw[Set.ext_iff] at *
      intro z
      constructor
      · intro zInConj
        rcases zInConj with ⟨w,⟨wInA,wEqz⟩⟩
        rw[Eq.comm, eq_mul_inv_iff_mul_eq, eq_inv_mul_iff_mul_eq,← mul_assoc] at wEqz
        rw[← wEqz,← xInNorm] at wInA
        change ∃ k ∈ A, x * k * x⁻¹ = x * z * x⁻¹ at wInA
        rcases wInA with ⟨s, ⟨sInA, sEqz⟩⟩
        simp only [eq_mul_inv_iff_mul_eq, Eq.comm, ← mul_assoc, ← eq_inv_mul_iff_mul_eq] at sEqz
        rw[mul_assoc, inv_mul_cancel, mul_one, one_mul] at sEqz
        rwa [← sEqz]
      · intro zInA
        rw[← xInNorm] at zInA
        change ∃ k ∈ A, x⁻¹ * k * x⁻¹⁻¹ = z
        change ∃ k ∈ A, x * k * x⁻¹ = z at zInA
        use x * z * x⁻¹
        constructor
        · rw[← xInNorm]
          change ∃ k ∈ A, x * k * x⁻¹ = x * z * x⁻¹
          use z
          constructor
          rwa[← xInNorm]
          rfl
        · simp only [← mul_assoc, inv_mul_cancel,inv_inv, one_mul]
          simp only [mul_assoc, inv_mul_cancel, mul_one]
  }
abbrev QuotientGroup (G : Type) [Group G] (K : Subgroup G) :=
  {x | ∃ g : G, leftCoset K g = x}
def subsetProd {G : Type} [Group G] (H K : Subgroup G) :=
  {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
def subsetInter {G : Type} [Group G] (A B : Subgroup G) :=
  {g : G | g∈(A:Set G) ∧ g∈(B:Set G) }
def funConverter {G H : Type} [Group G] [Group H] (f : G →* H) : homomorphism G H where
  --I only started using functions instead of my own half way through. So I had to make this.
  f := f
  hom := by
    intro a b
    exact f.map_mul a b
  oneMem := by
    exact f.map_one

-- The proof that f(1) = 1, where f is a homomorphism.
theorem kerProp1 {G H : Type} [Group G] [Group H] (φ : homomorphism G H) :
    φ.f (1) = 1 := by
  have h : φ.f (1) = φ.f (1 * 1) := by
    rw[mul_one 1]
  rw[φ.hom] at h
  nth_rewrite 1 [← one_mul (φ.f 1)] at h
  apply mul_right_cancel at h
  symm
  assumption

--The proof that f(g⁻¹)=(f(g))⁻¹, where f is a homomorphism.
theorem kerProp2 {G H : Type} [Group G] [Group H] (phi : homomorphism G H) :
    ∀ g : G, phi.f (g⁻¹) = ( phi.f (g) )⁻¹ := by
  intro g
  have h : phi.f (1) = phi.f (1) := rfl
  nth_rewrite 2 [← mul_inv_cancel g] at h
  rw[phi.hom] at h
  rw[kerProp1 phi] at h
  rw[← mul_inv_cancel (phi.f g)] at h
  apply mul_left_cancel at h
  symm
  assumption

--The proof that f(gⁿ)=(f(g))ⁿ, where f is a homomorphism, and n is an integer
theorem kerProp3 {G H : Type} [Group G] [Group H] (phi : homomorphism G H) :
    ∀ g : G, ∀ n : ℤ, phi.f (g^n) = ( phi.f (g) )^n := by
  intro g n
  induction n with
  | zero =>
    rw[zpow_zero g, zpow_zero (phi.f g)]
    apply kerProp1
  | succ k ih =>
    rw [zpow_add_one, phi.hom, zpow_add_one, ih]
  | pred k ih =>
    rw [zpow_sub_one, phi.hom, zpow_sub_one, ih, kerProp2]

--The proof that the kernel is a subgroup of its domain.
def kerProp4 {G H : Type} [Group G] [Group H] (φ : homomorphism G H) : Subgroup G := by
  refine {
    carrier := kern φ
    mul_mem' := by
      intro a b aInKern bInKern
      change φ.f (a * b) = 1
      rwa[φ.hom, aInKern, one_mul]
    one_mem' := by
      apply kerProp1 φ
    inv_mem' := by
      intro x xInKern
      change φ.f (x⁻¹) = 1
      rw[kerProp2,xInKern,inv_one]
  }
abbrev kernel {G H : Type} [Group G] [Group H] (φ : homomorphism G H) : Subgroup G :=
  (kerProp4 φ)

--The proof that the image of a homomorphism is a subgroup of its codomain.
def kerProp5 {G H : Type} [Group G] [Group H] (φ : homomorphism G H) : Subgroup H := by
  refine {
    carrier := kerIm φ
    mul_mem' := by
      intro a b aInIm bInIm
      change ∃ x : G, φ.f (x) = a * b
      rcases aInIm with ⟨x,xpa⟩
      rcases bInIm with ⟨y,ypa⟩
      use x * y
      rw[φ.hom,xpa,ypa]
    one_mem' := by
      use 1
      apply kerProp1
    inv_mem' := by
      intro y yInIm
      change ∃ x : G, φ.f (x) = y⁻¹
      rcases yInIm with ⟨a,apy⟩
      use a⁻¹
      rw[kerProp2,apy]
  }
abbrev KernImage {G H : Type} [Group G] [Group H] (φ : homomorphism G H) : Subgroup H :=
  (kerProp5 φ)

--The proofs that the set of cosets and the set of fibers over a are equivelant.
theorem Prop2a {G H : Type} [Group G] [Group H] (φ : homomorphism G H) (X : Set G)
    (hX : X ∈ {x | ∃ a : H, x = fiber φ a}) :
    ∀ u ∈ X, X = { u*k | k ∈ kernel φ} := by
  change ∃ a : H, X = fiber φ a at hX
  rcases hX with ⟨a, hXa⟩
  intro u uX
  ext z
  change z ∈ X ↔ z ∈ {x | ∃ k ∈ (kernel φ : Set G), u * k = x}
  change z ∈ X ↔ z ∈ {x | ∃ k ∈ {y | φ.f y = 1}, u * k = x}
  change z ∈ X ↔ ∃ k : G, φ.f k = 1 ∧ u * k = z
  constructor
  intro zX
  rw[hXa] at uX zX
  change φ.f z = a at zX
  change φ.f u = a at uX
  rw[← zX] at uX
  use u⁻¹ * z
  constructor
  rw[φ.hom,kerProp2,uX, inv_mul_cancel]
  rw[← mul_assoc, mul_inv_cancel,one_mul]
  intro h
  rw[hXa] at uX
  change u∈ {x | φ.f x = a} at uX
  change φ.f u = a at uX
  rw[hXa]
  change z∈{x | φ.f x = a}
  change φ.f z = a
  rcases h with ⟨k,KK⟩
  have phi : φ.f (u * k) = φ.f z := by
    rw[KK.2]
  rw[φ.hom,uX,KK.1,mul_one] at phi
  symm
  assumption
theorem Prop2b {G H : Type} [Group G] [Group H] (φ : homomorphism G H) (X : Set G)
    (hX : X ∈ {x | ∃ a : H, x = fiber φ a}) :
    ∀ u ∈ X, X = { k*u | k ∈ fiber φ 1} := by
  change ∃ a : H, X = fiber φ a at hX
  rcases hX with ⟨a, hXa⟩
  intro u uX
  ext z
  change z ∈ X ↔ z ∈ {x | ∃ k ∈ {y | φ.f y = 1}, k*u = x}
  change z ∈ X ↔ ∃ k : G, φ.f k = 1 ∧ k*u = z
  constructor
  intro zX
  rw[hXa] at uX zX
  change φ.f z = a at zX
  change φ.f u = a at uX
  rw[← zX] at uX
  use z * u⁻¹
  constructor
  rw[φ.hom,kerProp2,uX, mul_inv_cancel]
  rw[mul_assoc,inv_mul_cancel,mul_one]
  intro h
  rw[hXa] at uX
  change u∈ {x | φ.f x = a} at uX
  change φ.f u = a at uX
  rw[hXa]
  change z∈{x | φ.f x = a}
  change φ.f z = a
  rcases h with ⟨k,KK⟩
  have phi : φ.f (k * u) = φ.f z := by
    rw[KK.2]
  rw[φ.hom,uX,KK.1,one_mul] at phi
  symm
  assumption

--This Section Proves Quotient Groups are Groups.
lemma representationEquality {G : Type} [Group G] (K : Subgroup G) [K.Normal] :
    ∀ x y a b : G,
    leftCoset K x = leftCoset K a →
    leftCoset K y = leftCoset K b →
    leftCoset K (x * y) = leftCoset K (a * b) := by
  have hK : ∀ q ∈ K, ∀ g : G, g * q * g⁻¹ ∈ K :=
    (inferInstance : K.Normal).conj_mem
  intro m n a b hma hnb
  have hu : ∃ u ∈ K, a * u = m := by
    have h := (Set.ext_iff.mp hma) m
    change (∃ q ∈ K, m * q = m) ↔ (∃ q ∈ K, a * q = m) at h
    exact h.mp ⟨1, K.one_mem, by simp⟩
  have hv : ∃ v ∈ K, b * v = n := by
    have h := (Set.ext_iff.mp hnb) n
    change (∃ q ∈ K, n * q = n) ↔ (∃ q ∈ K, b * q = n) at h
    exact h.mp ⟨1, K.one_mem, by simp⟩
  rcases hu with ⟨u, huK, hmu⟩
  rcases hv with ⟨v, hvK, hnv⟩
  have hconj : b⁻¹ * u * b ∈ K := by
    have YY : b⁻¹ * u * b⁻¹⁻¹ ∈ K := hK u huK b⁻¹
    rwa[inv_inv] at YY
  ext z
  constructor
  · rintro ⟨k, hkK, hkz⟩
    refine ⟨(b⁻¹ * u * b) * v * k,
      K.mul_mem (K.mul_mem hconj hvK) hkK, ?_⟩
    calc
      (a * b) * ((b⁻¹ * u * b) * v * k) = (m * n) * k := by
        rw [← hmu, ← hnv]
        group
      _ = z := hkz
  · rintro ⟨k, hkK, hkz⟩
    have hvInv : v⁻¹ ∈ K := K.inv_mem hvK
    have hconjInv : (b⁻¹ * u * b)⁻¹ ∈ K := K.inv_mem hconj
    refine ⟨v⁻¹ * (b⁻¹ * u * b)⁻¹ * k,
      K.mul_mem (K.mul_mem hvInv hconjInv) hkK, ?_⟩
    calc
      (m * n) * (v⁻¹ * (b⁻¹ * u * b)⁻¹ * k) = (a * b) * k := by
        rw [← hmu, ← hnv]
        group
      _ = z := hkz

noncomputable def qmul {G : Type} [Group G] (K : Subgroup G) [K.Normal]
    (a b : {leftCoset K g | g : G}) : {leftCoset K g | g : G} := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  let g := Classical.choose ha
  let h := Classical.choose hb
  use leftCoset K (g * h)
  use (g * h)
noncomputable def qone {G : Type} [Group G] (K : Subgroup G) :
    {leftCoset K g | g : G} := by
  use leftCoset K 1
  use 1
noncomputable def qinv {G : Type} [Group G] (K : Subgroup G)
    (a : {leftCoset K g | g : G}) : {leftCoset K g | g : G} := by
  rcases a with ⟨a, ha⟩
  let g := Classical.choose ha
  use leftCoset K (g⁻¹)
  use g⁻¹

noncomputable instance {G : Type} [Group G] (K : Subgroup G) [K.Normal] :
    Group (QuotientGroup G K) where
  one := by
    exact qone K
  mul a b := qmul K a b
  mul_assoc := by
    intro a b c
    let g := Classical.choose a.property
    let h := Classical.choose b.property
    let i := Classical.choose c.property
    let ab := qmul K a b
    let bc := qmul K b c
    let j := Classical.choose ab.property
    let l := Classical.choose bc.property
    have hj : leftCoset K j = leftCoset K (g * h) := by
      change leftCoset K j = ab.val
      exact Classical.choose_spec ab.property
    have hl : leftCoset K l = leftCoset K (h * i) := by
      change leftCoset K l = bc.val
      exact Classical.choose_spec bc.property
    apply Subtype.ext
    change leftCoset K (j * i) = leftCoset K (g * l)
    calc
      leftCoset K (j * i) = leftCoset K ((g * h) * i) :=
      representationEquality K j i (g * h) i hj rfl
      _ = leftCoset K (g * (h * i)) := by rw [mul_assoc]
      _ = leftCoset K (g * l) := (representationEquality K g l g (h * i) rfl hl).symm
  one_mul := by
    intro a
    rcases a with ⟨aVal, aIsCoset⟩
    let e := Classical.choose (qone K).property
    let g := Classical.choose aIsCoset
    have he : leftCoset K e = leftCoset K 1 := by
      change leftCoset K e = (qone K).val
      exact Classical.choose_spec (qone K).property
    have hg : leftCoset K g = aVal := Classical.choose_spec aIsCoset
    apply Subtype.ext
    change leftCoset K (e * g) = aVal
    calc
      leftCoset K (e * g) = leftCoset K (1 * g) :=
      representationEquality K e g 1 g he rfl
      _ = leftCoset K g := by rw [one_mul]
      _ = aVal := hg
  mul_one := by
    intro a
    rcases a with ⟨aVal, aIsCoset⟩
    let e := Classical.choose (qone K).property
    let g := Classical.choose aIsCoset
    have he : leftCoset K e = leftCoset K 1 := by
      change leftCoset K e = (qone K).val
      exact Classical.choose_spec (qone K).property
    have hg : leftCoset K g = aVal := Classical.choose_spec aIsCoset
    apply Subtype.ext
    change leftCoset K (g * e) = aVal
    calc
      leftCoset K (g * e) = leftCoset K (g * 1) :=
      representationEquality K g e g 1 rfl he
      _ = leftCoset K g := by rw [mul_one]
      _ = aVal := hg
  inv a := by
    exact qinv K a
  inv_mul_cancel a := by
    rcases a with ⟨aVal, aIsCoset⟩
    let g := Classical.choose aIsCoset
    let invA := qinv K ⟨aVal, aIsCoset⟩
    let h := Classical.choose invA.property
    have hh : leftCoset K h = leftCoset K g⁻¹ := by
      change leftCoset K h = invA.val
      exact Classical.choose_spec invA.property
    apply Subtype.ext
    change leftCoset K (h * g) = leftCoset K 1
    calc
      leftCoset K (h * g) = leftCoset K (g⁻¹ * g) :=
        representationEquality K h g (g⁻¹) g hh rfl
      _ = leftCoset K 1 := by rw [inv_mul_cancel]

theorem Prop4a {G : Type} [Group G] (K : Subgroup G) :
    ∀ u v : G, (leftCoset K u = leftCoset K v) ↔ (v⁻¹ * u)∈ K := by
  intro u v
  constructor
  · intro cosetUisV
    have hmem : ∀ x, x ∈ leftCoset K u ↔ x ∈ leftCoset K v := Set.ext_iff.mp cosetUisV
    have memvu : (v * u) ∈ leftCoset K u ↔ (v * u) ∈ leftCoset K v := hmem (v * u)
    change (∃ k ∈ K, u * k = (v * u)) ↔ ∃ k ∈ K, v * k = (v * u) at memvu
    have memu := hmem u
    change (∃ k ∈ K, u * k = u) ↔ (∃ k ∈ K, v * k = u) at memu
    rcases memu.mp ⟨1, K.one_mem, by simp⟩ with ⟨k, hkK, hvk⟩
    have hvk' : v⁻¹ * u = k := by
      rw [← hvk, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hvk']
    exact hkK
  · intro vuK
    ext z
    constructor
    · intro zCosetu
      change ∃ k ∈ K, v * k = z
      change ∃ k ∈ K, u * k = z at zCosetu
      rcases zCosetu with ⟨k,hk⟩
      use  v⁻¹ * u * k
      constructor
      · exact K.mul_mem (vuK) hk.1
      · simp only [mul_assoc, mul_inv_cancel_left]
        exact hk.2
    · intro zCosetu
      change ∃ k ∈ K, v * k = z at zCosetu
      change ∃ k ∈ K, u * k = z
      rcases zCosetu with ⟨k,hk⟩
      use  u⁻¹ * v * k
      constructor
      · rw[← inv_inv (u⁻¹ * v),mul_inv_rev, inv_inv]
        exact K.mul_mem (K.inv_mem vuK) hk.1
      · simp only [mul_assoc, mul_inv_cancel_left]
        exact hk.2
theorem Prop4b {G : Type} [Group G] (K : Subgroup G) :
    Setoid.IsPartition {s : Set G | ∃ g : G, s = leftCoset K g} := by
  constructor
  · by_contra
    change ∃ g, ∅ = leftCoset K g at this
    rcases this with ⟨g,hg⟩
    have hmem : ∀ x, x ∈ ∅ ↔ x ∈ leftCoset K g := Set.ext_iff.mp hg
    have gmem : g ∈ ∅ ↔ g ∈ leftCoset K g := hmem g
    change (False ↔ g ∈ leftCoset K g) at gmem
    have gin : g ∈ leftCoset K g := by
      use 1
      constructor
      apply K.one_mem
      rw[mul_one]
    rcases gmem with ⟨FtoCos,CostoF⟩
    exact CostoF gin
  · intro a
    change ∃! b, (∃ g, b = leftCoset K g) ∧ a ∈ b
    use leftCoset K a
    constructor
    · change (∃ g, (leftCoset K a) = leftCoset K g) ∧ a ∈ leftCoset K a
      constructor
      · use a
      · use 1
        constructor
        · exact K.one_mem
        · simp
    · intro y hyp
      rcases hyp with ⟨existG, ainy⟩
      rcases existG with ⟨g,hg⟩
      rw[hg]
      rw[hg] at ainy
      clear y hg
      ext r
      change ∃ k ∈ K, g * k = a at ainy
      constructor
      · intro riny
        change ∃ k ∈ K, g * k = r at riny
        rcases ainy with ⟨a',⟨ainK,gaa⟩⟩
        rcases riny with ⟨r',⟨rinK,grr⟩⟩
        rw[← eq_mul_inv_iff_mul_eq] at grr
        rw[grr, mul_assoc,← eq_mul_inv_iff_mul_eq] at gaa
        have rina : ∃ k ∈ K, a * k = r := by
          use (r'⁻¹ * a')⁻¹
          constructor
          · apply K.inv_mem
            apply K.mul_mem
            · apply K.inv_mem
              exact rinK
            · exact ainK
          · symm
            exact gaa
        exact rina
      · intro rina
        change ∃ k ∈ K, a * k = r at rina
        rcases ainy with ⟨a',⟨ainK,gaa⟩⟩
        rcases rina with ⟨r',⟨rinK,arr⟩⟩
        rw[← eq_mul_inv_iff_mul_eq] at arr
        rw[arr, eq_mul_inv_iff_mul_eq, mul_assoc] at gaa
        have rina : ∃ k ∈ K, g * k = r := by
          use (a' * r')
          constructor
          · exact K.mul_mem ainK rinK
          · exact gaa
        exact rina

theorem Prop6a {G : Type} [Group G] (K : Subgroup G) :
    K.Normal ↔ ∀ g : G, leftCoset K g = rightCoset K g := by
  change K.Normal ↔ ∀ g : G, {x | ∃ k ∈ K, g * k = x} = {x | ∃ k ∈ K, k * g = x}
  constructor
  · intro kNormal g
    have normDef : ∀ q ∈ K, ∀ g : G, g * q * g⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem
    ext z
    change (∃ k ∈ K, g * k = z) ↔ ∃ k ∈ K, k * g = z
    constructor
    · intro zInLCoset
      rcases zInLCoset with ⟨x,hx⟩
      use g * x * g⁻¹
      constructor
      · exact normDef x hx.1 g
      · rw[mul_assoc, inv_mul_cancel g, mul_one]
        exact hx.2
    · intro zInRCoset
      rcases zInRCoset with ⟨x,hx⟩
      use g⁻¹ * x * g
      constructor
      · rw[← inv_inv g]
        nth_rewrite 1 [inv_inv g]
        exact normDef x hx.1 g⁻¹
      · simp only [← mul_assoc, mul_inv_cancel g, one_mul]
        exact hx.2
  · intro cosetEq
    have extZ : ∀ g z, z ∈ {x | ∃ k ∈ K, g * k = x} ↔ z ∈ {x | ∃ k ∈ K, k * g = x} := by
      intro g z
      have temp : ∀r, r ∈ {x | ∃ k ∈ K, g * k = x} ↔ r ∈ {x | ∃ k ∈ K, k * g = x} :=
        Set.ext_iff.mp (cosetEq g)
      apply temp z
    change ∀ g z, (∃ k ∈ K, g * k = z) ↔ (∃ k ∈ K, k * g = z) at extZ
    have extZForw : ∀ g z, (∃ k ∈ K, g * k = z) → (∃ k ∈ K, k * g = z) := by
      intro g z hz
      rwa[← extZ]
    have extZBack : ∀ g z, (∃ k ∈ K, k * g = z) → (∃ k ∈ K, g * k = z) := by
      intro g z hz
      rwa[extZ]
    clear extZ cosetEq
    constructor
    intro n nInK g
    rcases extZForw g (g * n) ⟨n, nInK, rfl⟩ with ⟨k, hkK, hkg⟩
    rw[← eq_mul_inv_iff_mul_eq] at hkg
    rw [← hkg]
    exact hkK
theorem Prop6b {G : Type} [Group G] (K : Subgroup G) :
    K.Normal ↔ ∀ g : G, conjugateSet K g ⊆ K := by
  constructor
  · intro kNormal g z zInConj
    have normDef : ∀ q ∈ K, ∀ g : G, g * q * g⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem
    change ∃ k ∈ K, g * k * g⁻¹ = z at zInConj
    rcases zInConj with ⟨k,hk⟩
    rw[← hk.2]
    exact (normDef k hk.1 g)
  · intro conjSubset
    constructor
    intro n nInK g
    have conjRW : ∀ (g z : G), (∃ k ∈ K, g * k * g⁻¹ = z) → z ∈ ↑K := by
      intro h z kConj
      rcases kConj with ⟨k,hk⟩
      rw[← hk.2]
      apply (conjSubset h)
      change ∃ q ∈ K, h * q * h⁻¹ = h * k * h⁻¹
      use k
      exact ⟨hk.1,rfl⟩
    have conjRW2 : (∃ k ∈ K, g * k *g⁻¹ = (g * n * g⁻¹)) → (g * n * g⁻¹) ∈ K :=
      conjRW g (g * n * g⁻¹)
    apply conjRW2
    use n

--Technically this prop was if and only if with K.Normal.
--But I can't define the other direction without presupposing K.Normal.
--So, I'm ignoring it, since the other direction is consequently trivially true.
theorem Prop7 {G : Type} [Group G] (K : Subgroup G) [K.Normal] :
    ∃ (φ : homomorphism G (QuotientGroup G K)), K = kernel φ := by
  have normDef : ∀ q ∈ K, ∀ g : G, g * q * g⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem
  let H := QuotientGroup G K
  let f (g : G) : H := ⟨leftCoset K g, ⟨g, rfl⟩⟩
  let φ : homomorphism G H := {
    f := f
    hom := by
      intro a b
      let x := Classical.choose (f a).property
      let y := Classical.choose (f b).property
      have hx : leftCoset K x = leftCoset K a := by
        change leftCoset K x = (f a).val
        exact Classical.choose_spec (f a).property
      have hy : leftCoset K y = leftCoset K b := by
        change leftCoset K y = (f b).val
        exact Classical.choose_spec (f b).property
      apply Subtype.ext
      change leftCoset K (a * b) = leftCoset K (x * y)
      exact (representationEquality K x y a b hx hy).symm
    oneMem := by
      rfl
  }
  use φ
  ext z
  change z ∈ K ↔ z ∈ (kernel φ : Set G)
  constructor
  · intro zInK
    ext y
    constructor
    · intro lCz
      change ∃ k ∈ K, 1 * k = y
      change ∃ k ∈ K, z * k = y at lCz
      rcases lCz with ⟨n,hn⟩
      rw[← hn.2]
      use z * n
      constructor
      · apply K.mul_mem zInK hn.1
      · rw[one_mul]
    · intro lC1
      change ∃ k ∈ K, 1 * k = y at lC1
      change ∃ k ∈ K, z * k = y
      rcases lC1 with ⟨n,hn⟩
      use z⁻¹ * n
      constructor
      · apply K.mul_mem (K.inv_mem zInK) hn.1
      · simp only [mul_inv_cancel,← mul_assoc]
        apply hn.2
  · intro zInKern
    have hcosets : leftCoset K z = leftCoset K 1 := congrArg Subtype.val zInKern
    have hmem : ∀ x : G, x ∈ leftCoset K z ↔ x ∈ leftCoset K 1 := Set.ext_iff.mp hcosets
    have hmem2 :(∃ k ∈ K, z * k = 1) ↔ ∃ k ∈ K, 1 * k = 1 := hmem 1
    have hmem3 : (∃ k ∈ K, 1 * k = 1) → (∃ k ∈ K, z * k = 1) := by
      rw[hmem2]
      intro a
      assumption
    have hmem4 : ∃ k ∈ K, 1 * k = 1 := by
      use 1
      rw[one_mul]
      exact ⟨K.one_mem, rfl⟩
    have hmem5 : (∃ k ∈ K, z * k = 1) := hmem3 hmem4
    rcases hmem5 with ⟨a,b⟩
    rw[← eq_mul_inv_iff_mul_eq, one_mul] at b
    rw[b.2]
    apply K.inv_mem b.1

lemma leftCoset1IsK {G : Type} [Group G] (K : Subgroup G) :
    K = leftCoset K 1 := by
  ext z
  constructor
  · intro zInK
    change ∃ k ∈ K, 1 * k = z
    use z
    rw[one_mul]
    exact ⟨zInK,rfl⟩
  · intro zInCoset
    change ∃ k ∈ K, 1 * k = z at zInCoset
    rcases zInCoset with ⟨k,hk⟩
    rw[one_mul] at hk
    rw[hk.2] at hk
    exact hk.1
lemma cosetSizeEq {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    ∀ g : G, Nat.card (leftCoset K 1) = Nat.card (leftCoset K g) := by
  intro g
  let e : {x : G // x ∈ leftCoset K 1} ≃
      {x : G // x ∈ leftCoset K g} := {
    toFun := fun x => ⟨g * x.val, by
      rcases x.property with ⟨k, hk, hx⟩
      refine ⟨k, hk, ?_⟩
      have hx' : k = x.val := by simpa using hx
      rw [← hx']
    ⟩
    invFun := fun x => ⟨g⁻¹ * x.val, by
      rcases x.property with ⟨k, hk, hx⟩
      refine ⟨k, hk, ?_⟩
      rw [one_mul, ← hx]
      group
    ⟩
    left_inv := by
      intro x
      apply Subtype.ext
      change g⁻¹ * (g * x.val) = x.val
      group
    right_inv := by
      intro x
      apply Subtype.ext
      change g * (g⁻¹ * x.val) = x.val
      group
  }
  exact Nat.card_congr e

theorem lagrangeTheoremA {G : Type} [Group G] [Finite G] (K : Subgroup G) [Finite K] :
    Nat.card G = Nat.card K * Nat.card {leftCoset K g | g : G}  := by
  let k := Nat.card K
  let g := Nat.card G
  let n := Nat.card {leftCoset K g | g : G}
  change g=k*n
  rcases Prop4b K with ⟨notNull, parts⟩
  have temp : {x | ∃ g, leftCoset K g = x} = {s | ∃ g, s = leftCoset K g} := by
    ext z
    change (∃ g, leftCoset K g = z) ↔ ∃ g, z= leftCoset K g
    simp [eq_comm]
  rw[← temp] at notNull
  rw[← temp] at parts
  clear temp
  have sizeK : K = leftCoset K 1 := leftCoset1IsK K
  have hKcard : Nat.card (leftCoset K 1) = k := by
    rw [← sizeK]
    rfl
  have hcosetCard (x : G) : Nat.card (leftCoset K x) = k := by
    rwa[← cosetSizeEq K x]
  have Qfin : {leftCoset K x | x : G}.Finite := by
    apply (Set.finite_range (fun g : G => leftCoset K g)).subset
    intro x hx
    rcases hx with ⟨g, hg⟩
    exact ⟨g, hg⟩
  have h_each (c : {leftCoset K x | x : G}) : Nat.card c.val = k := by
    rcases c.property with ⟨x, hx⟩
    rw [← hx]
    exact hcosetCard x
  let : Fintype {leftCoset K x | x : G} := Fintype.ofFinite {leftCoset K x | x : G}
  have hsum : (∑ c : {leftCoset K x | x : G}, Nat.card c.val) = k * n := by
    calc
      (∑ c : {leftCoset K x | x : G}, Nat.card c.val) = ∑ _c : {leftCoset K x | x : G}, k := by
        apply Finset.sum_congr rfl
        intro c hc
        exact h_each c
      _ = Fintype.card {leftCoset K x | x : G} * k := by simp
      _ = k * n := by
        rw [← Nat.card_eq_fintype_card]
        change Nat.card {leftCoset K x | x : G} * k = k * Nat.card {leftCoset K x | x : G}
        exact Nat.mul_comm _ _
  have hsum2 : (∑ c : {leftCoset K x | x : G}, Nat.card c.val) = g := by
    classical
    dsimp [g]
    rw [← Set.ncard_univ G]
    have hpartition : Setoid.IsPartition {c : Set G | ∃ x : G, leftCoset K x = c} :=⟨notNull, parts⟩
    rw [hpartition.ncard_eq_finsum (Set.univ : Set G)]
    rw [finsum_eq_sum_of_fintype]
    simp only [Set.univ_inter]
  rwa[hsum2] at hsum
theorem lagrangeTheoremB {G : Type} [Group G] [Finite G] (K : Subgroup G) [Finite K] :
    Nat.card K ∣ Nat.card G := by
  let k := Nat.card K
  let g := Nat.card G
  let n := Nat.card {leftCoset K g | g : G}
  use Nat.card {leftCoset K g | g : G}
  apply lagrangeTheoremA

--The Proof of the First Isomorphism Theorem
instance IsoTheorem1a
    {G H : Type} [Group G] [Group H]
    (φ : homomorphism G H) : (kernel φ).Normal := by
  constructor
  intro n hn g
  change g * n * g⁻¹ ∈ (kernel φ : Set G)
  change n ∈ (kernel φ : Set G) at hn
  change φ.f n = 1 at hn
  change φ.f (g * n * g⁻¹) = 1
  rw [φ.hom, φ.hom, hn, mul_one, kerProp2, mul_inv_cancel]
noncomputable def fitbMap {G H : Type} [Group G] [Group H] (φ : homomorphism G H) :
    QuotientGroup G (kernel φ) →* KernImage φ := by
  refine {
    toFun a := {
      val := by
        use φ.f (Classical.choose a.prop)
      property := by
        let b := (Classical.choose (a.prop))
        change φ.f b ∈ (KernImage φ : Set H)
        change ∃ x : G, φ.f (x) = φ.f (b)
        use b
      }
    map_one' := by
      ext
      change φ.f (Classical.choose ((1 : QuotientGroup G (kernel φ)).prop)) = 1
      let b := Classical.choose ((1 : QuotientGroup G (kernel φ)).prop)
      change φ.f b = 1
      have hbCoset : leftCoset (kernel φ) b = leftCoset (kernel φ) 1 :=
        Classical.choose_spec ((1 : QuotientGroup G (kernel φ)).prop)
      have hbmem : b ∈ leftCoset (kernel φ) b := by
        change ∃ k ∈ (kernel φ), b * k = b
        exact ⟨1, (kernel φ).one_mem, by simp⟩
      rw [hbCoset] at hbmem
      change ∃ k ∈ (kernel φ), 1 * k = b at hbmem
      rcases hbmem with ⟨k, hk, hkb⟩
      rw [one_mul] at hkb
      rw[hkb] at hk
      apply hk
    map_mul' a b := by
      ext
      dsimp
      let a' := Classical.choose (a.prop)
      let b' := Classical.choose (b.prop)
      let ab' := Classical.choose ((a * b).prop)
      change (φ.f (ab')) = φ.f (a') * φ.f (b')
      have ha' : a' ∈ (a : Set G) := by
        rw [← Classical.choose_spec (Subtype.prop a)]
        change ∃ k ∈ (kernel φ), a' * k = a'
        exact ⟨1, (kernel φ).one_mem, by simp⟩
      have hb' : b' ∈ (b : Set G) := by
        rw [← Classical.choose_spec (Subtype.prop b)]
        change ∃ k ∈ (kernel φ), b' * k = b'
        exact ⟨1, (kernel φ).one_mem, by simp⟩
      have hc' : ab' ∈ (a * b: Set G) := by
        rw [← Classical.choose_spec (Subtype.prop (a * b))]
        change ∃ k ∈ (kernel φ), ab' * k = ab'
        exact ⟨1, (kernel φ).one_mem, by simp⟩
      rw[← φ.hom]
      have abSet : ((a * b) : Set G) = leftCoset (kernel φ) (ab') := by
        let h := (a * b).property
        change ((a * b) : Set G) ∈ {x | ∃ g : G, leftCoset (kernel φ) g = x} at h
        change ∃ g : G, leftCoset (kernel φ) g = ((a * b) : Set G) at h
        symm
        apply Classical.choose_spec ((a*b).prop)
      have hprod : a' * b' ∈ (a * b : Set G) := by
        change a' * b' ∈ leftCoset (kernel φ) (a' * b')
        exact ⟨1, (kernel φ).one_mem, by simp⟩
      have hcoset : a' * b' ∈ leftCoset (kernel φ) ab' := by
        rw [← abSet]
        exact hprod
      rcases hcoset with ⟨k, hk, hmul⟩
      rw[← hmul, φ.hom, hk, mul_one]
  }
theorem IsoTheorem1b {G H : Type} [Group G] [Group H] (φ : homomorphism G H) :
    Nonempty ((QuotientGroup G (kernel φ)) ≃* (KernImage φ)) := by
  constructor
  have h_injective : Function.Injective (fitbMap φ) := by
    intro x y hxy
    apply Subtype.ext
    let x' := Classical.choose x.property
    let y' := Classical.choose y.property
    have hxyVal : φ.f x' = φ.f y' := by
      have h := congrArg (fun z : KernImage φ => (z : H)) hxy
      dsimp [fitbMap] at h
      exact h
    have hker : y'⁻¹ * x' ∈ kernel φ := by
      change y'⁻¹ * x' ∈ (kernel φ : Set G)
      change φ.f (y'⁻¹ * x') = 1
      rw [φ.hom, kerProp2, hxyVal, inv_mul_cancel]
    have hcoset : leftCoset (kernel φ) x' = leftCoset (kernel φ) y' :=
      (Prop4a (kernel φ) x' y').2 hker
    calc
      (x : Set G) = leftCoset (kernel φ) x' :=
        (Classical.choose_spec x.property).symm
      _ = leftCoset (kernel φ) y' := hcoset
      _ = (y : Set G) := Classical.choose_spec y.property
  have h_surjective : Function.Surjective (fitbMap φ) := by
    intro y
    have hyImage : (y : H) ∈ kerIm φ := by
      exact y.property
    rcases hyImage with ⟨g, hg⟩
    let x : QuotientGroup G (kernel φ) :=
      ⟨leftCoset (kernel φ) g, ⟨g, rfl⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    let g' := Classical.choose x.property
    have hcoset : leftCoset (kernel φ) g' = leftCoset (kernel φ) g :=
      Classical.choose_spec x.property
    have hker : g⁻¹ * g' ∈ kernel φ :=
      (Prop4a (kernel φ) g' g).1 hcoset
    have hkerSet : g⁻¹ * g' ∈ kern φ := by
      exact hker
    have hphi : (φ.f g)⁻¹ * φ.f g' = 1 := by
      change φ.f (g⁻¹ * g') = 1 at hkerSet
      rw [φ.hom, kerProp2] at hkerSet
      exact hkerSet
    change φ.f g' = (y : H)
    calc
      φ.f g' = φ.f g * ((φ.f g)⁻¹ * φ.f g') := by group
      _ = φ.f g * 1 := by rw [hphi]
      _ = φ.f g := by rw [mul_one]
      _ = (y : H) := hg
  exact MulEquiv.ofBijective (fitbMap φ) ⟨h_injective, h_surjective⟩

--The Proof of the Second Isomorphism Theorem
def IsoTheorem2a {G : Type} [Group G] ( A B : Subgroup G)
    (_hA : A ≤ normalizerSubgroup (B : Set G)) :
    Subgroup G := by
  refine {
    carrier := subsetProd A B
    mul_mem' := by
      let C := normalizerSubgroup (B : Set G)
      intro a b aInProd bInProd
      change ∃ h ∈ A, ∃ k ∈ B, a = h * k at aInProd
      change ∃ h ∈ A, ∃ k ∈ B, b = h * k at bInProd
      rcases aInProd with ⟨x,⟨xInA,a⟩⟩
      rcases bInProd with ⟨m,⟨mInA,b⟩⟩
      rcases a with ⟨y,⟨yInB,aEqxy⟩⟩
      rcases b with ⟨n,⟨nInB,bEqmn⟩⟩
      have ASubset : (A : Set G) ⊆ {g | conjugateSet B g = B} := by
        intro g hg
        exact _hA hg
      change ∀ z ∈ (A : Set G), {x | ∃ k ∈ B, z * k * z⁻¹ = x} = ↑B at ASubset
      replace ASubset :
      ∀ z ∈ (A : Set G), ∀ (y : G), y ∈ {x | ∃ k ∈ (B : Set G), z * k * z⁻¹ = x} ↔ y ∈ (B : Set G)
      := by
        intro r rmem k
        specialize ASubset r rmem
        rw[Set.ext_iff] at ASubset
        apply ASubset k
      change ∃ h ∈ A, ∃ k ∈ B, a * b = h * k
      change ∀ z ∈ ↑A, ∀ (y : G), (∃ k ∈ ↑B, z * k * z⁻¹ = y) ↔ y ∈ ↑B at ASubset
      rw[aEqxy, bEqmn]
      specialize ASubset m mInA
      specialize ASubset y
      rw[← ASubset] at yInB
      rcases yInB with ⟨k,⟨kInB, kEqy⟩⟩
      rw[Eq.comm, eq_mul_inv_iff_mul_eq] at kEqy
      rw[← mul_assoc, mul_assoc x y, kEqy,← mul_assoc, mul_assoc]
      use x*m
      constructor
      apply A.mul_mem' xInA mInA
      use k*n
      constructor
      apply B.mul_mem' kInB nInB
      rfl
    one_mem' := by
      use 1
      constructor
      apply A.one_mem'
      use 1
      constructor
      apply B.one_mem'
      rw[one_mul]
    inv_mem' := by
      intro x xInProd
      change ∃ h ∈ A, ∃ k ∈ B, x = h * k at xInProd
      change ∃ h ∈ A, ∃ k ∈ B, x⁻¹ = h * k
      rcases xInProd with ⟨r, ⟨rInA, xEqrk⟩⟩
      rcases xEqrk with ⟨s, ⟨sInB,xEqrs⟩⟩
      have hrNorm : conjugateSet B r = B := _hA rInA
      have hconj : r * s⁻¹ * r⁻¹ ∈ B := by
        change r * s⁻¹ * r⁻¹ ∈ (B : Set G)
        rw [← hrNorm]
        exact ⟨s⁻¹, B.inv_mem' sInB, rfl⟩
      use r⁻¹
      constructor
      apply A.inv_mem' rInA
      use r * s⁻¹ * r⁻¹
      constructor
      assumption
      rw[xEqrs, mul_inv_rev, ← mul_assoc, ← mul_assoc , inv_mul_cancel, one_mul]
  }
abbrev HKSubgroup {G : Type} [Group G] ( A B : Subgroup G)
  (_hA : A ≤ normalizerSubgroup (B : Set G)) :=
  IsoTheorem2a A B _hA
theorem IsoTheorem2b {G : Type} [Group G] ( A B : Subgroup G)
    (_hA : A ≤ normalizerSubgroup (B : Set G)) :
    B ≤ HKSubgroup A B _hA := by
  intro x xInB
  change ∃ a ∈ A, ∃ b ∈ B, x = a * b
  use 1
  constructor
  apply A.one_mem'
  use x
  constructor
  assumption
  rw[one_mul]
theorem IsoTheorem2c {G : Type} [Group G] ( A B : Subgroup G)
    (_hA : A ≤ normalizerSubgroup (B : Set G)) :
    (B.subgroupOf (HKSubgroup A B _hA)).Normal := by
  constructor
  intro b hb g
  change (b : G) ∈ B at hb
  change ((g * b * g⁻¹ : HKSubgroup A B _hA) : G) ∈ B
  have hgProd : (g : G) ∈ subsetProd A B := g.property
  change ∃ a ∈ A, ∃ c ∈ B, (g : G) = a * c at hgProd
  rcases hgProd with ⟨a, ha, c, hc, hg⟩
  have hcb : c * b * c⁻¹ ∈ B := by
    apply B.mul_mem' (B.mul_mem' hc hb)
    exact B.inv_mem' hc
  have haNorm : conjugateSet B a = B := _hA ha
  have hconj : a * (c * b * c⁻¹) * a⁻¹ ∈ B := by
    have hmem : a * (c * b * c⁻¹) * a⁻¹ ∈ conjugateSet B a :=
      ⟨c * b * c⁻¹, hcb, rfl⟩
    rw [haNorm] at hmem
    exact hmem
  change ((g : G) * (b : G) * (g : G)⁻¹) ∈ B
  rw [hg]
  simp only [mul_assoc] at hconj
  simpa only [mul_assoc, mul_inv_rev]
def IsoTheorem2d1 {G : Type} [Group G] ( A B : Subgroup G) : Subgroup G := by
  have TrivsubsetA : subsetInter A B ⊆ A := by
    intro x hx
    apply hx.1
  have TrivsubsetB : subsetInter A B ⊆ B := by
    intro x hx
    apply hx.2
  refine {
    carrier := subsetInter A B
    mul_mem' := by
      intro a b aInInter bInInter
      have aInAnB : a ∈ A ∧ a ∈ B := by
        exact ⟨TrivsubsetA aInInter, TrivsubsetB aInInter⟩
      have bInAnB : b ∈ A ∧ b ∈ B := by
        exact ⟨TrivsubsetA bInInter, TrivsubsetB bInInter⟩
      have abInA : (a*b)∈ A := by
        apply A.mul_mem' aInAnB.1 bInAnB.1
      have abInB : (a*b)∈ B := by
        apply B.mul_mem' aInAnB.2 bInAnB.2
      constructor
      apply abInA
      apply abInB
    one_mem' := by
      constructor
      apply A.one_mem'
      apply B.one_mem'
    inv_mem' := by
      intro x xInInter
      rcases xInInter with ⟨xInA, xInB⟩
      apply A.inv_mem' at xInA
      apply B.inv_mem' at xInB
      exact ⟨ xInA, xInB⟩
  }
abbrev subgroupInter {G : Type} [Group G] ( A B : Subgroup G) :=
  IsoTheorem2d1 A B
theorem IsoTheorem2d2 {G : Type} [Group G] ( A B : Subgroup G)
    (_hA : A ≤ normalizerSubgroup (B : Set G)) :
    (subgroupInter A B) ≤ A := by
  intro x hx
  apply hx.1
theorem IsoTheorem2e {G : Type} [Group G] ( A B : Subgroup G)
    (_hA : A ≤ normalizerSubgroup (B : Set G)) :
    ((subgroupInter A B).subgroupOf (A)).Normal  := by
  constructor
  intro n nInInter a
  change (n : G) ∈ (subgroupInter A B) at nInInter
  change (a * n * a⁻¹ : G) ∈ (subgroupInter A B)
  constructor
  · apply A.mul_mem' (A.mul_mem' a.property n.property) (A.inv_mem' a.property)
  · have nInB : (n : G) ∈ (B : Set G) := by
      apply nInInter.2
    have aInNorm : (a⁻¹ : G) ∈ normalizerSubgroup (B : Set G) := by
      apply (normalizerSubgroup (B : Set G)).inv_mem' (_hA a.property)
    change conjugateSet B (a⁻¹ : G) = B at aInNorm
    rw[ Set.ext_iff] at aInNorm
    specialize aInNorm n
    rw[← aInNorm] at nInB
    change  ∃ k ∈ B, (↑a)⁻¹ * k * (a)⁻¹⁻¹ = n at nInB
    rcases nInB with ⟨x,⟨xInB, anaX⟩⟩
    rw[inv_inv,← eq_mul_inv_iff_mul_eq, Eq.comm, eq_inv_mul_iff_mul_eq,← mul_assoc] at anaX
    simp
    rwa[← anaX] at xInB
def sitf1Map {G : Type} [Group G] (A B : Subgroup G)
    (_hA : A ≤ normalizerSubgroup (B : Set G)) :
    (letI : (B.subgroupOf (HKSubgroup A B _hA)).Normal := IsoTheorem2c A B _hA
    letI : ((subgroupInter A B).subgroupOf A).Normal := IsoTheorem2e A B _hA
    A →* QuotientGroup ((HKSubgroup A B _hA)) (B.subgroupOf (HKSubgroup A B _hA))) := by
  letI := IsoTheorem2c A B _hA
  letI := IsoTheorem2e A B _hA
  have simple : ∀ (x : A), (x : G) ∈ HKSubgroup A B _hA := by
    intro x
    change (x : G) ∈ subsetProd A B
    change ∃ a ∈ A, ∃ b ∈ B, (x : G) = a * b
    exact ⟨x, x.property, 1, B.one_mem', by simp⟩
  refine {
    toFun := fun x =>{
      val := leftCoset (B.subgroupOf (HKSubgroup A B _hA)) ⟨(x : G), simple x⟩
      property := by
        use ⟨↑x, simple x⟩
    }
    map_one' := by
      rfl
    map_mul' := by
      intro x y
      apply Subtype.ext
      let K := B.subgroupOf (HKSubgroup A B _hA)
      let xHK : ↥(HKSubgroup A B _hA) := ⟨(x : G), simple x⟩
      let yHK : ↥(HKSubgroup A B _hA) := ⟨(y : G), simple y⟩
      let qx : QuotientGroup (↥(HKSubgroup A B _hA)) K :=
        ⟨leftCoset K xHK, ⟨xHK, rfl⟩⟩
      let qy : QuotientGroup (↥(HKSubgroup A B _hA)) K :=
        ⟨leftCoset K yHK, ⟨yHK, rfl⟩⟩
      change leftCoset K ⟨(x * y : A), simple (x * y)⟩ =
        (qmul K qx qy).val
      change leftCoset K ⟨(x * y : A), simple (x * y)⟩ =
        leftCoset K (Classical.choose qx.property * Classical.choose qy.property)
      have hx : leftCoset K (Classical.choose qx.property) = leftCoset K xHK := by
        simpa [qx] using Classical.choose_spec qx.property
      have hy : leftCoset K (Classical.choose qy.property) = leftCoset K yHK := by
        simpa [qy] using Classical.choose_spec qy.property
      symm
      exact representationEquality K
        (Classical.choose qx.property) (Classical.choose qy.property)
        xHK yHK hx hy
  }
def sitf2Map {G : Type} [Group G] (A B : Subgroup G)
    (_hA : A ≤ normalizerSubgroup (B : Set G)) :
    (letI : (B.subgroupOf (HKSubgroup A B _hA)).Normal := IsoTheorem2c A B _hA
    letI : ((subgroupInter A B).subgroupOf A).Normal := IsoTheorem2e A B _hA
    (HKSubgroup A B _hA)→* QuotientGroup ((HKSubgroup A B _hA)) (B.subgroupOf (HKSubgroup A B _hA)))
    := by
  letI := IsoTheorem2c A B _hA
  letI := IsoTheorem2e A B _hA
  have simple : ∀ (x : (HKSubgroup A B _hA)), (x : G) ∈ HKSubgroup A B _hA := by
    intro x
    exact x.property
  refine {
    toFun := fun x =>{
      val := leftCoset (B.subgroupOf (HKSubgroup A B _hA)) ⟨(x : G), simple x⟩
      property := by
        use ⟨↑x, simple x⟩
    }
    map_one' := by
      rfl
    map_mul' := by
      intro x y
      apply Subtype.ext
      let K := B.subgroupOf (HKSubgroup A B _hA)
      let xHK : ↥(HKSubgroup A B _hA) := ⟨(x : G), simple x⟩
      let yHK : ↥(HKSubgroup A B _hA) := ⟨(y : G), simple y⟩
      let qx : QuotientGroup (↥(HKSubgroup A B _hA)) K :=
        ⟨leftCoset K xHK, ⟨xHK, rfl⟩⟩
      let qy : QuotientGroup (↥(HKSubgroup A B _hA)) K :=
        ⟨leftCoset K yHK, ⟨yHK, rfl⟩⟩
      change leftCoset K ⟨(x * y : (HKSubgroup A B _hA)), simple (x * y)⟩ =
        (qmul K qx qy).val
      change leftCoset K ⟨(x * y : (HKSubgroup A B _hA)), simple (x * y)⟩ =
        leftCoset K (Classical.choose qx.property * Classical.choose qy.property)
      have hx : leftCoset K (Classical.choose qx.property) = leftCoset K xHK := by
        simpa [qx] using Classical.choose_spec qx.property
      have hy : leftCoset K (Classical.choose qy.property) = leftCoset K yHK := by
        simpa [qy] using Classical.choose_spec qy.property
      symm
      exact representationEquality K
        (Classical.choose qx.property) (Classical.choose qy.property)
        xHK yHK hx hy
  }
theorem IsoTheorem2f {G : Type} [Group G] (A B : Subgroup G)
    (_hA : A ≤ normalizerSubgroup (B : Set G)) :
    (letI : (B.subgroupOf (HKSubgroup A B _hA)).Normal := IsoTheorem2c A B _hA
     letI : ((subgroupInter A B).subgroupOf A).Normal := IsoTheorem2e A B _hA
     Nonempty ((QuotientGroup (↥(HKSubgroup A B _hA)) (B.subgroupOf (HKSubgroup A B _hA))) ≃*
        (QuotientGroup (↥A) ((subgroupInter A B).subgroupOf A)))) := by
  let this1 : (B.subgroupOf (HKSubgroup A B _hA)).Normal := IsoTheorem2c A B _hA
  let this2 : ((subgroupInter A B).subgroupOf A).Normal := IsoTheorem2e A B _hA
  let φ := funConverter (sitf1Map A B _hA)
  have firstIso : Nonempty (↑(QuotientGroup (A) (kernel φ)) ≃* ↥(KernImage φ)) := by
    apply IsoTheorem1b φ
  have hImageAll :
    ∀ q : QuotientGroup (HKSubgroup A B _hA)
        (B.subgroupOf (HKSubgroup A B _hA)),
      q ∈ KernImage φ := by
    intro q
    have qProp : ∃ g : (HKSubgroup A B _hA), leftCoset (B.subgroupOf (HKSubgroup A B _hA)) g = q
      := q.property
    rcases qProp with ⟨ab,LcosetAB⟩
    change q ∈ (KernImage φ).carrier
    change ∃ x : A, φ.f (x) = q
    have abProp : ∃ a ∈ A, ∃ b ∈ B, (ab.val : G) = (a : G) * (b : G) := ab.property
    rcases abProp with ⟨a,aInA,b,bInB,abEq⟩
    let K := B.subgroupOf (HKSubgroup A B _hA)
    let aHK : HKSubgroup A B _hA :=
      ⟨a, by
        change a ∈ subsetProd A B
        exact ⟨a, aInA, 1, B.one_mem', by simp⟩⟩
    let bHK : HKSubgroup A B _hA :=
      ⟨b, IsoTheorem2b A B _hA bInB⟩
    have hbK : bHK ∈ K := by
      change (b : G) ∈ B
      exact bInB
    have hBcoset : leftCoset K bHK = leftCoset K (1 : HKSubgroup A B _hA) := by
      ext x
      change (∃ k ∈ K, bHK * k = x) ↔ (∃ k ∈ K, (1 : HKSubgroup A B _hA) * k = x)
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨bHK * k, K.mul_mem hbK hk, by simp⟩
      · rintro ⟨k, hk, hx⟩
        refine ⟨bHK⁻¹ * k, K.mul_mem (K.inv_mem hbK) hk, ?_⟩
        calc
          bHK * (bHK⁻¹ * k) = k := by group
          _ = x := by simpa using hx
    have hab : ab = aHK * bHK := by
      apply Subtype.ext
      exact abEq
    have hCosets := representationEquality K aHK bHK aHK 1 rfl hBcoset
    have habCoset : leftCoset K ab = leftCoset K aHK := by
      rw [hab]
      simpa using hCosets
    refine ⟨⟨a, aInA⟩, ?_⟩
    apply Subtype.ext
    change leftCoset K aHK = q.val
    exact habCoset.symm.trans LcosetAB
  have kernEqB : kernel φ = ((subgroupInter A B).subgroupOf A) := by
    ext z
    constructor
    · intro zInKern
      change z ∈ (kern φ) at zInKern
      change φ.f z = 1 at zInKern
      replace zInKern :
        φ.f z =(1 :↑(QuotientGroup (↥(HKSubgroup A B _hA)) (B.subgroupOf (HKSubgroup A B _hA)))).val
        := by
        rw[zInKern]
      rw[Set.ext_iff] at zInKern
      rw [Subgroup.mem_subgroupOf]
      change ↑z∈(A:Set G) ∧ ↑z∈(B:Set G)
      constructor
      · exact z.property
      · have zinNorm : z.val ∈ normalizerSubgroup ↑B := by
          apply _hA z.property
        change conjugateSet B z.val = B at zinNorm
        change {x | ∃ k ∈ B, z * k * z⁻¹ = x} = B at zinNorm
        rw[Set.ext_iff] at zinNorm
        have hzHK : (z : G) ∈ HKSubgroup A B _hA := by
          change ∃ h ∈ A, ∃ k ∈ B, (z : G) = h * k
          use z
          constructor
          apply z.property
          use 1
          constructor
          apply B.one_mem'
          rw[mul_one]
        specialize zInKern ⟨(z : G), hzHK⟩
        have hmem : (⟨(z : G), hzHK⟩ : ↥(HKSubgroup A B _hA)) ∈ (φ.f z : Set _) := by
          use 1
          constructor
          apply B.one_mem'
          rw[mul_one]
        rw[zInKern] at hmem
        obtain ⟨k, hk, hx⟩ := hmem
        rw[one_mul] at hx
        rwa[hx] at hk
    · intro zInInter
      rw [Subgroup.mem_subgroupOf] at zInInter
      rcases zInInter with ⟨zInA,zInB⟩
      change φ.f z = 1
      apply Subtype.ext
      rw[Set.ext_iff]
      intro x
      constructor
      · intro xInPhi
        rcases xInPhi with ⟨y,yInB,zyx⟩
        symm at zyx
        have hxG : (x : G) = (z : G) * (y : G) := by
          simpa using congrArg Subtype.val zyx
        have hxB : (x : G) ∈ B := by
          rw [hxG]
          exact B.mul_mem zInB (Subgroup.mem_subgroupOf.mp yInB)
        use x
        constructor
        assumption
        rw[one_mul]
      · intro xInOne
        rcases xInOne with ⟨y,yInB,zyx⟩
        rw[one_mul] at zyx
        rw[← zyx]
        have hzHK : (z : G) ∈ HKSubgroup A B _hA := by
          change ∃ h ∈ A, ∃ k ∈ B, (z : G) = h * k
          use z
          constructor
          apply z.property
          use 1
          constructor
          apply B.one_mem'
          rw[mul_one]
        have hzS : (⟨(z : G), hzHK⟩ : ↥(HKSubgroup A B _hA)) ∈ B.subgroupOf (HKSubgroup A B _hA) :=
          Subgroup.mem_subgroupOf.mpr zInB
        refine ⟨⟨(z : G), hzHK⟩⁻¹ * y, ?_, ?_⟩
        · exact (B.subgroupOf _).mul_mem ((B.subgroupOf _).inv_mem hzS) yInB
        · rw[← mul_assoc, mul_inv_cancel, one_mul]
  obtain ⟨e⟩ := firstIso
  constructor
  let e2 : ↑(QuotientGroup (↥(HKSubgroup A B _hA)) (B.subgroupOf (HKSubgroup A B _hA)))
        ≃* ↥(KernImage φ) :=
  { toFun := fun q => ⟨q, hImageAll q⟩
    invFun := fun p => p.1
    left_inv := fun q => rfl
    right_inv := fun p => rfl
    map_mul' := fun a b => rfl }
  have key : ∀ (K : Subgroup A) [K.Normal], kernel φ = K →
    (↑(QuotientGroup (↥A) (kernel φ)) ≃* ↑(QuotientGroup (↥A) K)) := by
    intro K _ h
    subst h
    exact MulEquiv.refl _
  let e3 := key _ kernEqB
  exact e2.trans (e.symm.trans e3)

end Oset
