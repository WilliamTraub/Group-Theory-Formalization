variable {G : Type u} {H : Type v}

def Set (α : Type u) := α → Prop
def Set.mem {α : Type u} (S : Set α) (a : α) := S a
instance {α : Type u} : Membership α (Set α) := ⟨Set.mem⟩


class semigroup (G : Type u) where
  mul : G -> G -> G
  mul_assoc : ∀ Q B C : G, (mul Q (mul B C)) = (mul (mul Q B) C)

class monoid (G : Type U) extends semigroup G where
  id : G
  mul_id : ∀ Q : G, (mul Q id) = Q
  id_mul : ∀ Q : G, (mul id Q) = Q

-- I would make group extend monoid but I don't want to have to call monoid.mul in proofs
class Group (G : Type u) where
  mul : G -> G -> G
  mul_assoc : ∀ Q B C : G, (mul Q (mul B C)) = (mul (mul Q B) C)
  id : G
  inv : G -> G
  mul_id : ∀ Q : G, (mul Q id) = Q
  id_mul : ∀ Q : G, (mul id Q) = Q
  inv_mul : ∀ Q : G, (mul (inv Q) Q) = id

def gpow [Group G] (a : G) : Int → G
  | Int.ofNat n => Nat.rec Group.id (fun _ x => Group.mul x a) n
  | Int.negSucc n => Nat.rec Group.id (fun _ x => Group.mul x (Group.inv a)) (n + 1)

class CyclicGroup [Group G] : Prop where
  generated : ∃ a : G, ∀ g : G, ∃ n : Int, gpow a n = g

infixl:70 " * " => Group.mul
postfix:max "⁻¹" => Group.inv
notation "e" => Group.id

theorem id_unique [Group G] (a b : G)
  (ha : ∀ g : G, a * g = g ∧ g * a = g)
  (hb : ∀ g : G, b * g = g ∧ g * b = g) :
  a = b := by
  have h1 : a * b = b := (ha b).1
  have h2 : a * b = a := (hb a).2
  rw [← h2, h1]

theorem left_cancellation [Group G] (a b c : G) : a * b = a * c <-> b = c := by
  constructor
  intro h
  have h2 : a⁻¹ * (a * b) = a⁻¹ * (a * c) := congrArg (Group.mul a⁻¹) h
  rw [Group.mul_assoc, Group.mul_assoc, Group.inv_mul, Group.id_mul, Group.id_mul] at h2
  exact h2

  intro hb
  rw [hb]

theorem mul_inv [Group G] (a : G) : a * a⁻¹ = e := by
  have h1 : a * a⁻¹ * (a * a⁻¹) = a * a⁻¹ := by
    have : a⁻¹ * (a * a⁻¹) = a⁻¹ := by
      rw [Group.mul_assoc, Group.inv_mul, Group.id_mul]
    calc a * a⁻¹ * (a * a⁻¹)
        = a * (a⁻¹ * (a * a⁻¹)) := by rw [<- Group.mul_assoc]
      _ = a * a⁻¹               := by rw [this]
  have h2 : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = (a * a⁻¹)⁻¹ * (a * a⁻¹) :=
    congrArg (Group.mul (a * a⁻¹)⁻¹) h1
  rw [Group.mul_assoc, Group.inv_mul, Group.id_mul] at h2
  exact h2


theorem inv_id [Group G] : (Group.id : G)⁻¹ = Group.id := by
  have h : (Group.id : G)⁻¹ * Group.id = Group.id := Group.inv_mul Group.id
  rwa [Group.mul_id] at h

theorem double_inv [Group G] (a : G) : a⁻¹⁻¹ = a := by
  have h1 : a⁻¹ * a⁻¹⁻¹ = e := mul_inv a⁻¹
  have h2 : a⁻¹ * a = e := Group.inv_mul a
  have h3 : a * a⁻¹ * a⁻¹⁻¹ = a * a * a⁻¹ := by
    rw [<- Group.mul_assoc, h1, Group.mul_id, <- Group.mul_assoc, mul_inv, Group.mul_id]
  rw [mul_inv, <- Group.mul_assoc, mul_inv, Group.mul_id, Group.id_mul] at h3
  exact h3

class subgroup [Group G] (S : Set G) : Prop where
  mul_mem : ∀ {a b}, a ∈ S -> b ∈ S -> a * b ∈ S
  id_mem : (e : G) ∈ S
  inv_mem : ∀ {a}, a ∈ S -> a⁻¹ ∈ S

def trivial_subgroup [Group G] : Set G := fun a => a = e

class normal_subgroup [Group G] (S : Set G) : Prop extends subgroup S where
  normal : ∀ n ∈ S, ∀ g : G, g * n * g⁻¹ ∈ S

theorem trivial_normal [Group G] : normal_subgroup (trivial_subgroup (G := G)) where
  id_mem := rfl
  mul_mem := by
    intro a b ha hb
    unfold trivial_subgroup
    rw [ha, hb, Group.mul_id]
    rfl
  inv_mem := by
    intro a ha
    unfold trivial_subgroup at ha
    rw [ha, inv_id]
    rfl
  normal := by
    intro a ha g
    unfold trivial_subgroup at ha
    rw [ha, Group.mul_id, mul_inv]
    rfl

structure group_hom [Group G] [Group H] where
  toFun : G → H
  map_mul : ∀ a b : G, toFun (a * b) = toFun a * toFun b

structure GroupIso [Group G] [Group H] extends group_hom (G := G) (H := H) where
  inv : H → G
  left_inv : ∀ a : G, inv (toFun a) = a
  right_inv : ∀ b : H, toFun (inv b) = b

-- Quiz 1
-- 1: Give an example of a semigroup which is not a monoid. Prove your statement.
def PosInt := {n : Nat // n > 0}
instance PosInt.semigroup : semigroup PosInt where
  mul a b := ⟨a.val + b.val, by have := a.property; omega⟩
  mul_assoc a b c := by
    apply Subtype.ext
    simp [Nat.add_assoc]

-- It suffices to show that if there is no identity in the positive integers under addition, it is not a semigroup.
theorem PosInt_no_identity :
  ¬ ∃ i : PosInt, ∀ a : PosInt,
    PosInt.semigroup.mul a i = a ∧ PosInt.semigroup.mul i a = a := by
  intro ⟨i, hi⟩
  have ha := (hi ⟨1, by omega⟩).1
  have hval : (1 : Nat) + i.val = 1 := congrArg Subtype.val ha
  have := i.property
  omega

theorem inv_mul_rev [Group G] (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h : (a * b) * (b⁻¹ * a⁻¹) = e := by
    rw [<- Group.mul_assoc, Group.mul_assoc b, mul_inv, Group.id_mul, mul_inv]
  have h2 : (a * b)⁻¹ * ((a * b) * (b⁻¹ * a⁻¹)) = (a * b)⁻¹ * e :=
    congrArg (Group.mul (a * b)⁻¹) h
  rw [Group.mul_assoc, Group.inv_mul, Group.id_mul, Group.mul_id] at h2
  exact h2.symm

-- Helpers about homomorphisms
theorem hom_id [Group G] [Group H] (φ : group_hom (G := G) (H := H)) :
    φ.toFun e = e := by
  have h : φ.toFun e = φ.toFun e * φ.toFun e := by
    rw [← φ.map_mul, Group.id_mul]
  have h2 : (φ.toFun e)⁻¹ * φ.toFun e = (φ.toFun e)⁻¹ * (φ.toFun e * φ.toFun e) :=
    congrArg (Group.mul (φ.toFun e)⁻¹) h
  rw [Group.inv_mul, Group.mul_assoc, Group.inv_mul, Group.id_mul] at h2
  exact h2.symm

theorem hom_inv [Group G] [Group H] (φ : group_hom (G := G) (H := H)) (a : G) :
    φ.toFun a⁻¹ = (φ.toFun a)⁻¹ := by
  have h : φ.toFun a * φ.toFun a⁻¹ = e := by
    rw [← φ.map_mul, mul_inv, hom_id]
  have h2 : (φ.toFun a)⁻¹ * (φ.toFun a * φ.toFun a⁻¹) = (φ.toFun a)⁻¹ * e :=
    congrArg (Group.mul (φ.toFun a)⁻¹) h
  rw [Group.mul_assoc, Group.inv_mul, Group.id_mul, Group.mul_id] at h2
  exact h2

def ker [Group G] [Group H] (φ : group_hom (G := G) (H := H)) : Set G :=
  fun a => φ.toFun a = e

theorem ker_normal [Group G] [Group H] (φ : group_hom (G := G) (H := H)) :
    normal_subgroup (ker φ) where
  id_mem := hom_id φ

  mul_mem := by
    intro a b ha hb
    show φ.toFun (a * b) = e
    rw [φ.map_mul, ha, hb, Group.mul_id]

  inv_mem := by
    intro a ha
    show φ.toFun (a)⁻¹ = e
    rw [hom_inv, ha, inv_id]

  normal := by
    intro k hk g
    show φ.toFun (g * k * g⁻¹) = e
    rw [φ.map_mul, φ.map_mul, hom_inv, hk, Group.mul_id, mul_inv]

-- Cosets
def left_coset [Group G] (g : G) (S : Set G) : Set G :=
  fun x => ∃ n, n ∈ S ∧ x = g * n

-- Coset equivalence relation
def coset_rel [Group G] (S : Set G) (a b : G) : Prop :=
  a⁻¹ * b ∈ S

-- An equivalence relation is reflexitive, symmetric, and transitive
theorem coset_rel_refl [Group G] (S : Set G) [subgroup S] (a : G) : coset_rel S a a := by
  show a⁻¹ * a ∈ S
  rw [Group.inv_mul]
  exact subgroup.id_mem

theorem coset_rel_symm [Group G] (S : Set G) [subgroup S] {a b : G} (h : coset_rel S a b) :
    coset_rel S b a := by
  rw [coset_rel]
  show b⁻¹ * a ∈ S
  have h1 := subgroup.inv_mem h
  rw [inv_mul_rev, double_inv] at h1
  exact h1

theorem coset_rel_trans [Group G] (S : Set G) [subgroup S] {a b c : G}
    (h1 : coset_rel S a b) (h2 : coset_rel S b c) : coset_rel S a c := by
  show a⁻¹ * c ∈ S
  rw [coset_rel] at h1 h2
  have h3 : a⁻¹ * b * (b⁻¹ * c) ∈ S := subgroup.mul_mem h1 h2
  rw [Group.mul_assoc] at h3
  rw [<- Group.mul_assoc a⁻¹, mul_inv, Group.mul_id] at h3
  exact h3

def coset_setoid [Group G] (S : Set G) [subgroup S] : Setoid G where
  r := coset_rel S
  iseqv := ⟨coset_rel_refl S, coset_rel_symm S, coset_rel_trans S⟩

-- Quotient group
def QuotientGroup [Group G] (S : Set G) [subgroup S] : Type u :=
  Quotient (coset_setoid S)

-- Quotient map universal property

-- Lagrange
-- First isomorphism theorem
