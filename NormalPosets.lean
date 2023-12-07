import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Lattice
import Mathlib.Algebra.Hom.Group.Defs
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Partial
import Mathlib.Data.PFun
import Mathlib.Order.Category.PartOrd
import Mathlib.Algebra.Free
import Mathlib.GroupTheory.Subsemigroup.Basic
import Mathlib.GroupTheory.Subsemigroup.Operations

#check Quot
section Coerciones

variable {α : Type u} {a b c d : α}
def injective (f : X → Y) : Prop :=
∀ ⦃x₁ x₂⦄, f x₁ = f x₂ → x₁ = x₂

def surjective (f : X → Y) : Prop :=
∀ y, ∃ x, f x = y

def bijective (f : X → Y) := injective f ∧ surjective f
def curry {α β γ : Type u} (f : α × β → γ) : α → β → γ := λ x y => f (x, y)

def uncurry {α β γ : Type u} (f : α → β → γ) : α × β → γ := fun (x, y) => f x y


def range (f : α → β) : Set β :=
  { b | ∃ a, b = f a }
def Ordrange {α : Type u} {β : Type u} [Preorder α][Preorder β] (f : OrderHom α β) : Set β :=
   { b | ∃ a : α, b = f a }

def cod_res (f : α → β) (s : Set β) (h: range f ⊆ s): α → s := fun x => --Achica el codominio de una función
  have h₁ : ∃ a, f x = f a := by
    use x
  have h₂ : f x ∈ range f := by
    apply h₁
  have h₃ : f x ∈ s := by
    apply h
    apply h₂
  ⟨f x, h₃⟩

def res (f : α → β) (s : Set α) : α →. β := --de PFun
  (PFun.lift f).restrict s.subset_univ

def asSubtype (f : α →. β) (s : f.Dom) : β := --de PFun
  f.fn s s.2

instance SubPoset {α : Type u} [PartialOrder α] {p : Set α} : PartialOrder p where
  le_antisymm := by
    intro x y xley ylex
    apply le_antisymm xley ylex

def OrdHomRestrict' [PartialOrder α] [PartialOrder β] (f : OrderHom α β)(p : Set α) : p → β := fun x =>
  asSubtype (res f.toFun p) x --Toma un homomorfismo f de α en β y un subconjunto p de α y devuelve f restringido a p (como función)

theorem RestIsMon  [PartialOrder α] [PartialOrder β] {f : OrderHom α β} {p : Set α} : Monotone (OrdHomRestrict' f p) := by --la restricción de homomorfismos de orden es monotona
  intro x y xley
  apply f.monotone'
  simp
  apply xley

  def OrdHomRestrict [PartialOrder α] [PartialOrder β] (f : OrderHom α β)(p : Set α) : p →o β := -- Da la restricción como homomorfismo de orden
 {toFun := OrdHomRestrict' f p
  monotone' := by apply RestIsMon}

  def OrdHomRange' [PartialOrder α] [PartialOrder β] (f : OrderHom α β)(p : Set α) (q : Set β) (c : Ordrange (OrdHomRestrict f p) ⊆ q): p → q :=
    have h' : range (OrdHomRestrict' f p) ⊆ q := by
      intro x xir
      rcases xir with ⟨a, ha⟩
      apply c
      constructor
      have h'' : (OrdHomRestrict f p) a = x := by
        calc
          (OrdHomRestrict f p) a = (OrdHomRestrict' f p) a := by apply Eq.refl
          _ = x := by rw[ha]
      apply Eq.symm
      apply h''
    cod_res (OrdHomRestrict' f p) q h'

  theorem RestrictionMonotone [PartialOrder α] [PartialOrder β] {f : OrderHom α β}{p : Set α} {q : Set β} {c : Ordrange (OrdHomRestrict f p) ⊆ q} : Monotone (OrdHomRange' f p q c) := by
    intro x y xley
    calc
      (OrdHomRange' f p q c) x = (OrdHomRestrict' f p) x:= by apply Eq.refl
      _ = f x := by apply Eq.refl
      _ ≤ f y := by
        apply f.monotone'
        apply xley

def OrdHomRange [PartialOrder α] [PartialOrder β] (f : OrderHom α β)(p : Set α) (q : Set β) (c : range (OrdHomRestrict' f p) ⊆ q ): p →o q :=
 {toFun := OrdHomRange' f p q c
  monotone' := RestrictionMonotone
  }

  structure OrderIsomorphism (α β : Type u) [PartialOrder α] [PartialOrder β] extends OrderHom α β where
    bij := bijective toFun
    iso := ∀ x y : α, toFun x ≤ toFun y  → x ≤ y

  def IsIso {α β : Type u} [PartialOrder α] [PartialOrder β] (f : OrderHom α β) : Prop :=
    bijective f ∧   ∀ x y : α, f x ≤ f y  → x ≤ y
end Coerciones

section RightNormalBand


class RightNormalBand (α : Type u) extends Semigroup α where --Definición de banda normal a derecha
  mul_idem : ∀ a : α , a * a = a
  mul_norm : ∀ a b c : α ,  a * b * c = b * a * c

theorem NormIsReg {α : Type u} [RightNormalBand α] { x y : α} : x * y * x = y * x := by -- Las bandas normales a derecha son regulares
  calc
    x * y * x = y * x * x := by apply RightNormalBand.mul_norm
    _ = y * (x * x) := by apply mul_assoc
    _ = y * x := by rw[RightNormalBand.mul_idem]

namespace RightNormalBand

variable [RightNormalBand α] {a b c d : α}

def leq (a b : α) := a * b = a --aca defino una relación binaria. Los siguientes teoremas son para mostrar que es un orden parcial

@[simp]
theorem refl_le {α : Type u} [RightNormalBand α]: ∀ a : α, leq a a := by
  intro a
  have h' : a * a = a := by apply RightNormalBand.mul_idem
  apply h'

@[simp]
theorem trans_le' (h : a * b = a) (h' : b * c = b) : a * c = a := by
calc
     a * c = a * b * c := by
      rw [h]
    _ = a * (b * c) := by
      rw [mul_assoc]
    _ = a * b := by
      rw [h']
    _ = a := by
      rw[h]

theorem trans_le : ∀ (a b c : α), leq a b → leq b c → leq a c := by
  apply trans_le'

theorem antisymm_le' (h : a * b = a) (h' : b * a = b) : a = b := by
calc
     a = a * b := by rw[h]
     _ = a * (b * a) := by rw[h']
     _= a * b * a := by rw[← mul_assoc]
     _= b * a * a := by rw[RightNormalBand.mul_norm]
     _= b * (a * a) := by rw[mul_assoc]
     _= b * a := by rw[RightNormalBand.mul_idem]
     _ = b := by rw[h']

theorem antisymm_le : ∀ (a b : α), leq a b → leq b a → a = b := by
  apply antisymm_le'
  done

instance orden_parcial : PartialOrder α where
  le := leq
  le_refl := refl_le
  le_trans := trans_le
  le_antisymm := antisymm_le


lemma por_is_leq' {α : Type u} [RightNormalBand α]: ∀ (a b : α),leq (a * b) b := by --Muestra que un producto siempre es menor que el elemento derecho
  intro a b
  have h : (a * b) * b = a * b :=
    calc
     a * b * b = a * (b * b)  := by rw[mul_assoc]
     _ = a * b := by rw[RightNormalBand.mul_idem]
  apply h

@[simp]
lemma por_is_leq {α : Type u} [RightNormalBand α]: ∀ (a b : α), (a * b) ≤ b := by
  apply por_is_leq'


def Closed {α : Type u} [Mul α] (S : Set α) : Prop := --Defino que un conjunto sea cerrado bajo el producto
  ∀ x y :α, x ∈ S → y ∈ S → x * y ∈ S
def Decrec {α : Type u } [PartialOrder α] (S : Set α) : Prop := --Definición de conjunto decreciente
  ∀ x y :α , x ∈ S → y ≤ x → y ∈ S

lemma InitIsDec' {α : Type u} [PartialOrder α] (a : α) : Decrec (Set.Iic a):= by --Prueba de que los segmentos iniciales son decrecientes
  intro x y
  intro h h'
  have h'' : x ≤ a := by apply h
  have h''' : y ≤ a := by apply le_trans h' h''
  apply h'''


lemma DecIsSub {α : Type u} [RightNormalBand α] (S : Set α) (h : Decrec S) : Closed S := by --Prueba de que en una banda normal los decrecientes son cerrados
  intro x y
  have h' : x * y ≤ y:= by apply por_is_leq
  show_term
  intro _ h'''
  apply h
  apply h'''
  apply h'

end RightNormalBand
end RightNormalBand

section NormalPosets
instance SegmentoInicial {α : Type u} [PartialOrder α] {a : α} : PartialOrder (Set.Iic a) where
  le_antisymm := by
    intro x y
    apply le_antisymm

def InitialSegment {α : Type u} [PartialOrder α] (a : α) : Set α := {b | b ≤ a}


def IsNormal {α : Type u} (_ : PartialOrder α) : Prop := --Existe una RNB \alpha tal que P es isomorfo al poset asociado a α
∃ (α': Type u),∃(_ : RightNormalBand α'), ∃(_:OrderIso α α'), True

theorem RestrictionInitial {α β: Type u} [PartialOrder α] [PartialOrder β] {f : α →o β} {b : α}: Ordrange (OrdHomRestrict f (Set.Iic  b)) ⊆ Set.Iic (f b) := by
    intro x xir
    rcases xir with ⟨w, hw⟩
    have
    have g : ∀ z : Set.Iic b, z ≤ b  := by
      simp_all
    have h'' : x ≤ f b := by
      calc
        x = (OrdHomRestrict f (Set.Iic b)) w := by apply hw
        _ = f w := by apply Eq.refl
        _ ≤ f b := by
          apply f.monotone'
          apply g
    have h''' : ∀ z : β, z ≤ f b → z ∈ Set.Iic (f b) := by simp_all
    apply h'''
    apply h''
    apply this

def InitialRestriction {α β: Type u} [PartialOrder α] [PartialOrder β] (f : OrderHom α β)(a : α)  : Set.Iic a →o Set.Iic (f a) :=
    OrdHomRange f (Set.Iic a) (Set.Iic (f a)) (RestrictionInitial)

def IsNormal' {α : Type u} (_ : PartialOrder α) : Prop :=
∃ (α' : Type u), ∃(_ : SemilatticeInf α'), ∃(f : OrderHom α α'), ∀(a : α), IsIso (InitialRestriction f a)

end NormalPosets

section Subestructuras

-- variable {S : Type*} [RightNormalBand α] [SetLike  S α] [hA : MulMemClass S α] (s : S

def Closed [RightNormalBand α] (p : Set α) : Prop := ∀ x y : α, x ∈ p → y ∈ p → x * y ∈ p

variable {α : Type u} [RightNormalBand α]

def ProdRestrict {s : Set α} {h : Closed s} : s → s → s :=
fun x y =>
  ⟨x * y, by apply h
             · apply x.2
             · apply y.2 ⟩



theorem RestricIdem {s : Set α} {h : Closed s} : ∀ x : s, ProdRestrict (s:= s) (h := h) x x = x := by
  intro x
  calc
    ProdRestrict (s:= s) (h := h) x x = ⟨x * x, _ ⟩ := by apply Eq.refl
    _ = ⟨x, by simp⟩ := by simp_all [RightNormalBand.mul_idem]
    _ = x := by simp_all


theorem RestricAsoc {s : Set α} {h : Closed s} : ∀ x y z: s, ProdRestrict (s:=s) (h:=h) (ProdRestrict (s:=s) (h:=h) x y) z = ProdRestrict (s:=s) (h:=h) x (ProdRestrict (s:=s) (h:=h) y z)  := by
  intro x y z
  calc
    ProdRestrict (s:=s) (h:=h) (ProdRestrict (s:=s) (h:=h) x y) z = ⟨x * y * z, _⟩ := by apply Eq.refl
    _ = ⟨x * (y * z), by
                      apply h
                      · simp
                      · apply h
                        · simp
                        · simp⟩ := by simp_all[mul_assoc]
    _ = ProdRestrict (s:=s) (h:=h) x (ProdRestrict (s:=s) (h:=h) y z) := by apply Eq.refl

theorem RestricNorm {s : Set α} {h : Closed s} : ∀ x y z: s, ProdRestrict (s:=s) (h:=h) (ProdRestrict (s:=s) (h:=h) x y) z = ProdRestrict (s:=s) (h:=h) (ProdRestrict (s:=s) (h:=h) y x) z := by
  intro x y z
  calc
     ProdRestrict (s:=s) (h:=h) (ProdRestrict (s:=s) (h:=h) x y) z = ⟨x * y * z, _⟩ := by apply Eq.refl
    _ = ⟨y * x * z , by
                      apply h
                      apply h
                      simp_all
                      simp
                      simp
                      ⟩ := by simp_all[RightNormalBand.mul_norm]
    _ = ProdRestrict (s:=s) (h:=h) (ProdRestrict (s:=s) (h:=h) y x) z := by apply Eq.refl



@[default_instance]
instance SubBanda {s : Set α} {h : Closed s}: RightNormalBand s where
  mul := ProdRestrict (s := s) (h := h)
  mul_assoc := RestricAsoc
  mul_norm :=  RestricNorm
  mul_idem := RestricIdem

#check SubBanda

def HomRestrict'' [RightNormalBand β] (f : MulHom α β) (s : Set α) : s → β :=  asSubtype (res f.toFun s)

def HomRestrict' [RightNormalBand β] (f : MulHom α β) (s : Set α) {h : Closed s} {SubBanda : Mul s}  : MulHom s  β where
  toFun := HomRestrict'' f s
  map_mul' :=  by
    intro x y
    calc
      HomRestrict'' f s (x * y) = res f.toFun s (x * y) := by
        apply Eq.refl
      _ = f (x * y) := by apply Eq.refl
      _ = (f x) * (f y) := by apply f.map_mul'
      _ =  (res f.toFun s x) * (res f.toFun s y) := by apply Eq.refl
      _ = HomRestrict'' f s x * HomRestrict'' f s y := by apply Eq.refl



end Subestructuras

section Productos
instance BandProduct [RightNormalBand α] [RightNormalBand β] : RightNormalBand (α × β) where
  mul_idem := by
    intro x
    have h' : x.fst * x.fst = x.fst := by apply RightNormalBand.mul_idem
    have h'' : x.snd * x.snd = x.snd := by apply RightNormalBand.mul_idem
    calc
      x * x = (x.fst * x.fst, x.snd * x.snd) := by apply Eq.refl
      _ = (x.fst, x.snd) := by
        rw[h']
        rw[h'']
  mul_norm := by
    intro x y z
    calc
      x * y * z = (x.fst * y.fst * z.fst, x.snd * y.snd * z.snd) := by apply Eq.refl
      _ = (y.fst * x.fst * z.fst, y.snd * x.snd * z.snd) := by
        simp_all[RightNormalBand.mul_norm]

end Productos
section Homomorfismos
 --instance HomImage' [RightNormalBand α] [Mul β] {f : MulHom α β} {h : surjective f.toFun} : RightNormalBand β where
    --mul_assoc := by
      --intro a b c
      --have ha : ∃ a' : α, f a' = a := by apply h
      --have hb : ∃ a' : α, f a' = b := by apply h
      --have hc : ∃ a' : α, f a' = c := by apply h
      --rcases ha with ⟨a', ha'⟩
      --rcases hb with ⟨b', hb'⟩
      --rcases hc with ⟨c', hc'⟩
      --calc
       -- a * b * c = (f a') * (f b') * (f c') := by simp_all[ha', hb', hc']
       -- _ = f (a' * b') * f c' := by rw[map_mul]
        --_ = f (a' * b' * c') := by rw[←map_mul]
        --_-- = f (a' * (b' * c')) := by
        --  rw[mul_assoc]
        --_ = f a' * f (b' * c') := by rw[map_mul]
        --_ = f a' * (f b' * f c') := by rw[map_mul]
        --_ = a * (b * c) := by simp_all[ha', hb', hc']
    --mul_idem := by
      --  intro a
       -- have ha : ∃ a' : α, f a' = a := by apply h
        --rcases ha with ⟨a', ha'⟩
        --calc
        --  a * a = f a' * f a' := by simp_all[ha']
       --   _ = f (a' * a') := by rw[←map_mul]
        --  _ = f (a') := by rw[RightNormalBand.mul_idem]
         -- _ = a := by rw[ha']
    --mul_norm := by
     -- intro a b c
      --have ha : ∃ a' : α, f a' = a := by apply h
      --have hb : ∃ a' : α, f a' = b := by apply h
      --have hc : ∃ a' : α, f a' = c := by apply h
      --rcases ha with ⟨a', ha'⟩
      --rcases hb with ⟨b', hb'⟩
      --rcases hc with ⟨c', hc'⟩
      --calc
       -- a * b * c = (f a') * (f b') * (f c') := by simp_all[ha', hb', hc']
       -- _ = f (a' * b') * f c' := by rw[map_mul]
        --_ = f (a' * b' * c') := by rw[←map_mul]
        --_ = f (b' * a' * c') := by rw[RightNormalBand.mul_norm]
        --_ = f (b' * a') * f c' := by rw[map_mul]
        --_ = (f b' * f a') * f c' := by rw[map_mul]
        --_ = b * a * c:= by simp_all[ha', hb', hc']


def BandHomtoOrdHom {α β :Type u} [RightNormalBand α][RightNormalBand β] (f : MulHom α β) : α →o β where
  toFun := f.toFun
  monotone' := by
    intro x y xley
    have h' : x * y = x := by
      apply xley
    have h'' : (f.toFun x) * (f.toFun y) = f.toFun x := by
      calc
        (f.toFun x) * (f.toFun y) = f.toFun (x * y) := by
          rw[f.map_mul']
        _ = f.toFun x := by simp_all[h']
    apply h''



theorem BandIsoisOrdIso {α β : Type u} [RightNormalBand α][RightNormalBand β] {f : MulHom α β} {h : bijective f.toFun}: IsIso (BandHomtoOrdHom f) := by
  constructor
  apply h
  intro x y fxy
  have g : (f.toFun (x * y)) = f.toFun x := by
    calc
      (f.toFun (x * y)) = (f.toFun x) *(f.toFun y) := by apply f.map_mul'
      _ = f.toFun x := by apply fxy
  have g'' : x * y = x:= by
    apply h.left
    rw[g]
  apply g''
end Homomorfismos
section Congruencias

class Congruence (α : Type u) [RightNormalBand α] where

  r : α → α → Prop

  refl  : ∀ x, r x x

  symm  : ∀ {x y}, r x y → r y x

  trans : ∀ {x y z}, r x y → r y z → r x z

  cong : ∀ {x y z w}, r x y → r z w → r (x * z) (y * w)


#check Quot.ind

def Cociente {α : Type u} [RightNormalBand α] (h : Congruence α) : Type u :=
  Quot h.r
theorem QuotForm {α : Type u} [RightNormalBand α] {h : Congruence α} : ∀ x : Quot h.r, ∃x' : α, x = Quot.mk h.r x' := by
  apply Quot.ind
  intro a
  have h' : Quot.mk h.r a = Quot.mk h.r a := by apply Eq.refl
  apply Exists.intro a h'



def ProjCann' {α : Type u} [RightNormalBand α] {h : Congruence α} : α → Quot h.r := fun a => Quot.mk h.r a



theorem ProjCongr'' {α : Type u} [RightNormalBand α] {h : Congruence α} : ∀ x y z : α,  h.r y z → Quot.mk h.r (x * y) = Quot.mk h.r (x * z) := by
intro x y z yrz
have h' : h.r (x * y) (x *z) := by
  apply h.cong
  apply h.refl
  apply yrz
exact Quot.sound h'

theorem ProjCongr' {α : Type u} [RightNormalBand α] {h : Congruence α} : ∀ y z x : α,  h.r y z → Quot.mk h.r (y * x) = Quot.mk h.r (z * x) := by
intro y z x yrz
have h' : h.r (y * x) (z *x) := by
  apply h.cong
  apply yrz
  apply h.refl
exact Quot.sound h'
def QuotProd  {α : Type u} [RightNormalBand α] {h : Congruence α} : Quot h.r → Quot h.r →  Quot h.r :=
  Quot.lift₂ (β := α) (γ := Quot h.r) (r := h.r) (s := h.r) (f := fun x y => Quot.mk h.r (x * y)) (hr := ProjCongr'') (hs := ProjCongr' (α := α))

theorem QuotProdAssoc {α : Type u} [RightNormalBand α] {h : Congruence α} : ∀ a b c : Quot h.r, QuotProd (QuotProd a b) c = QuotProd a (QuotProd b c) := by
  intro a b c
  have g : ∃ a' : α, a = Quot.mk h.r a' := by apply QuotForm
  rcases g with ⟨a', ha⟩
  have g' : ∃ b' : α, b = Quot.mk h.r b' := by apply QuotForm
  rcases g' with ⟨b', hb⟩
  have g'' : ∃ c' : α, c = Quot.mk h.r c' := by apply QuotForm
  rcases g'' with ⟨c', hc⟩
  calc
    QuotProd (QuotProd a b) c = QuotProd (Quot.mk h.r (a' * b')) (Quot.mk h.r c') := by
      simp_all[ha,hb,hc]
      apply Eq.refl
    _ = Quot.mk h.r (a' * b' * c') := by apply Eq.refl
    _ = Quot.mk h.r (a' *(b' * c')) := by rw[mul_assoc]
    _ = QuotProd (Quot.mk h.r a') (Quot.mk h.r (b' * c')) := by apply Eq.refl
    _ = QuotProd a (QuotProd b c) := by
      simp_all[ha,hb,hc]
      apply Eq.refl

theorem QuotProdIdem {α : Type u} [RightNormalBand α] {h : Congruence α} : ∀ a : Quot h.r, QuotProd a a = a := by
  intro a
  have g : ∃ a' : α, a = Quot.mk h.r a' := by apply QuotForm
  rcases g with ⟨a', ha⟩
  calc
    QuotProd a a = Quot.mk h.r (a' * a') := by
      simp_all[ha]
      apply Eq.refl
    _= Quot.mk h.r a' := by
      rw[RightNormalBand.mul_idem]
    _ = a := by rw[ha]


theorem QuotProdNorm {α : Type u} [RightNormalBand α] {h : Congruence α} : ∀ a b c : Quot h.r, QuotProd (QuotProd a b) c = QuotProd (QuotProd b a) c := by
  intro a b c
  have g : ∃ a' : α, a = Quot.mk h.r a' := by apply QuotForm
  rcases g with ⟨a', ha⟩
  have g' : ∃ b' : α, b = Quot.mk h.r b' := by apply QuotForm
  rcases g' with ⟨b', hb⟩
  have g'' : ∃ c' : α, c = Quot.mk h.r c' := by apply QuotForm
  rcases g'' with ⟨c', hc⟩
  calc
    QuotProd (QuotProd a b) c = QuotProd (Quot.mk h.r (a' * b')) (Quot.mk h.r c') := by
      simp_all[ha,hb,hc]
      apply Eq.refl
    _ = Quot.mk h.r (a' * b' * c') := by apply Eq.refl
    _ = Quot.mk h.r (b' * a' * c') := by rw[RightNormalBand.mul_norm]
    _ = QuotProd (Quot.mk h.r (b' * a')) (Quot.mk h.r c') := by apply Eq.refl
    _ = QuotProd (QuotProd b a) c := by
      simp_all[ha,hb,hc]
      apply Eq.refl

 instance QuotBand {α : Type u} [RightNormalBand α] {h : Congruence α} : RightNormalBand (Quot h.r) where
  mul := QuotProd
  mul_assoc := QuotProdAssoc
  mul_idem := QuotProdIdem
  mul_norm := QuotProdNorm



def ProjCann {α : Type u} [RightNormalBand α] {h : Congruence α} : MulHom α (Quot h.r) where
  toFun := ProjCann'
  map_mul' := by
    intro x y
    calc
      ProjCann' (x * y) = Quot.mk h.r (x * y) := by apply Eq.refl
      _ = (Quot.mk h.r x) * (Quot.mk h.r y) := by apply Eq.refl
def Project  [RightNormalBand α] (a b : α) := a * b = b ∧ b * a = a

theorem ProjectRefl [RightNormalBand α]  {a : α} : Project a a := by
  have h' : a * a = a := by apply RightNormalBand.mul_idem
  have h'' : a * a = a ∧ a * a = a := by
    rename_i inst
    simp_all only [and_self]
  apply h''

theorem ProjectSymm [RightNormalBand α]  {a b: α} : Project a b → Project b a := by
  intro x
  constructor
  apply x.right
  apply x.left

theorem ProjectTrans [RightNormalBand α] {a b c : α} : Project a b → Project b c → Project a c := by
  intro x y
  constructor
  rw[← y.left]
  rw[← mul_assoc]
  rw[x.left]
  rw[← x.right]
  rw[← mul_assoc]
  rw[y.right]

theorem ProjectCongr [RightNormalBand α]  {a b c d : α} :  Project a b → Project c d → Project (a * c) (b * d) := by
  intro x y
  constructor
  calc
    a * c * (b * d) = a * (c * (b * d)):= by rw[mul_assoc]
    _= a * (c * (d * b * d)) := by rw[NormIsReg]
    _ = a * (c * (d * (b * d))) := by rw[mul_assoc]
     _ = a * (c * d * (b * d)) := by rw[mul_assoc]
     _ = a * (d * (b * d)) := by rw[y.left]
     _ = a * (d * b * d) := by rw[mul_assoc]
     _ = a * (b * d) := by rw[NormIsReg]
     _ = a * b * d := by rw[mul_assoc]
     _ = b * d := by rw[x.left]

  calc
    b * d * (a * c) = b * (d * (a * c)):= by rw[mul_assoc]
    _= b * (d * (c * a * c)) := by rw[NormIsReg]
    _ = b * (d * (c * (a * c))) := by rw[mul_assoc]
     _ = b * (d * c * (a * c)) := by rw[mul_assoc]
     _ = b * (c * (a * c)) := by rw[y.right]
     _ = b * (c * a * c) := by rw[mul_assoc]
     _ = b * (a * c) := by rw[NormIsReg]
     _ = b * a * c := by rw[mul_assoc]
     _ = a * c := by rw[x.right]


instance ProjectCong [RightNormalBand α]  : Congruence α where
  r := Project
  refl := by
    intro x
    apply ProjectRefl
  symm := by
    intro x y1
    apply ProjectSymm
  trans := by
    intro x y z
    apply ProjectTrans
  cong := by
    intro x y z w
    apply ProjectCongr

theorem ProductProject [RightNormalBand α] : ∀ a b :α, Project (a * b) (b * a) := by
  intro a b
  have h' : (a * b) * (b * a) = b * a ∧ (b * a) * (a * b) = a * b := by
    constructor
    calc
      a * b * (b * a) = a * (b * b * a) := by
        rw[mul_assoc]
        rw[←mul_assoc b b a]
      _ = a * (b * a) := by rw[RightNormalBand.mul_idem]
      _ = a * b * a := by rw[mul_assoc]
      _ = b * a := by apply NormIsReg
    calc
      b * a * (a * b) = b * (a * a * b) := by
        rw[mul_assoc]
        rw[←mul_assoc a a b]
      _ = b * (a * b) := by rw[RightNormalBand.mul_idem]
      _ = b * a * b := by rw[mul_assoc]
      _ = a * b := by apply NormIsReg
  apply h'

theorem ProjectQuotComm [RightNormalBand α] : ∀ a b :Quot Project, QuotProd (α := α) a b = QuotProd (α := α) b a := by
  intro a b
  have g : ∃ a' : α, a = Quot.mk Project a' := by apply QuotForm
  rcases g with ⟨a', ha⟩
  have g' : ∃ b' : α, b = Quot.mk Project b' := by apply QuotForm
  rcases g' with ⟨b', hb⟩
  calc
   QuotProd a b  = Quot.mk Project (a' * b') := by
      simp_all[ha,hb]
      apply Eq.refl
    _ = Quot.mk Project (b' * a'):= by
      apply Quot.sound
      apply ProductProject
    _ = QuotProd b a :=  by
      simp_all[ha,hb]
      apply Eq.refl

theorem QuotInfRight [RightNormalBand α] : ∀ a b: Quot Project, QuotProd (α := α) b a ≤ a := by
  intro a b
  apply RightNormalBand.por_is_leq

theorem QuotInfLeft [RightNormalBand α] : ∀ a b: Quot Project, QuotProd (α := α) a b ≤ a := by
  intro a b
  rw[ProjectQuotComm]
  apply QuotInfRight

theorem QuotInf [RightNormalBand α] : ∀ a b c : Quot Project, QuotBand.leq a b → QuotBand.leq a c → QuotBand.leq a (QuotProd (α := α) b c) := by
  intro a b c aleb alec
  have h' : QuotProd a b = a ∧ QuotProd a c = a := by
    constructor
    apply aleb
    apply alec
  have h'' : QuotProd a (QuotProd b c) = a := by
    calc
      QuotProd a (QuotProd b c) = QuotProd (QuotProd a b) c := by
        rw[QuotProdAssoc]
      _ = a := by
        rw[h'.left]
        rw[h'.right]
  apply h''

instance QuotSemilattice [RightNormalBand α] : SemilatticeInf (Quot Project (α:= α)) where
  inf := QuotProd
  le := QuotBand.leq
  le_refl := QuotBand.refl_le
  le_trans := QuotBand.trans_le
  le_antisymm := QuotBand.antisymm_le
  inf_le_left := QuotInfLeft
  inf_le_right := QuotBand.por_is_leq
  le_inf := QuotInf

--def OrderProjection [RightNormalBand α] : α →o Quot Project (α:= α) where
 -- toFun := ProjCann'
  --monotone' := by
   -- intro x y xley
    --have h' : ProjCann'

end Congruencias

section Semilattices

variable {α : Type u} [SemilatticeInf α]


theorem SLNorm : ∀ a b c : α, a ⊓ b ⊓ c = b ⊓ a ⊓ c := by
  intro a b c
  simp [inf_comm]

instance SemilatticeNormal : RightNormalBand α where
  mul := Inf.inf
  mul_assoc := by apply inf_assoc
  mul_norm := SLNorm
  mul_idem := by apply inf_idem

theorem SemilatticeRespect [SemilatticeInf α] {x y : α} : SemilatticeNormal.leq x y ↔ x ≤ y := by
constructor
intro xley
have h' : x ⊓ y = x := by apply xley
simp_all[h', inf_le_right]
apply xley
intro xy
have h' : x ⊓ y = x := by
  apply le_antisymm
  exact Eq.le xy
  exact Eq.ge xy
apply h'

end Semilattices
section Antichains
variable {α : Type u}
namespace Anticadenas
class Antichain (α : Type u) extends PartialOrder α where
  incomp : ∀ (x y : α), x ≤ y → x = y

--instance Anticadena : Antichain α where
 -- le := Eq
  --le_refl := Eq.refl
  --le_trans := by
   -- intro a b c ab bc
    --calc
     -- a = b := by apply ab
      --_ = c := by apply bc
  --le_antisymm := by
   -- intro a b ab _
    --apply ab
  --incomp := by
   -- intro x y xley
    --simp_all

def AntichainProd [Antichain α] : Mul α  where
  mul := fun _ y => y

theorem ACProdAssoc [Antichain α] :∀ a b c : α,  AntichainProd.mul (AntichainProd.mul a b) c = AntichainProd.mul a (AntichainProd.mul b c) := by
  intro a b c
  calc
    AntichainProd.mul (AntichainProd.mul a b) c =  AntichainProd.mul b c := by
      apply Eq.refl
    _ = AntichainProd.mul a (AntichainProd.mul b c) := by
      apply Eq.refl

theorem ACProdRefl [Antichain α] :∀ a : α, AntichainProd.mul a a = a := by apply Eq.refl

theorem ACProdNorm [Antichain α]: ∀ a b c : α, AntichainProd.mul (AntichainProd.mul a b) c = AntichainProd.mul (AntichainProd.mul b a) c := by
  intro a b c
  calc
    AntichainProd.mul (AntichainProd.mul a b) c = c := by apply Eq.refl
    _ = AntichainProd.mul (AntichainProd.mul b a) c := by apply Eq.refl

instance AntichainNormal [Antichain α] : RightNormalBand α where
  mul := AntichainProd.mul
  mul_assoc := ACProdAssoc
  mul_norm := ACProdNorm
  mul_idem := ACProdRefl

theorem AntichainRespect [h : Antichain α] {x y : α} : AntichainNormal.leq x y ↔ x ≤ y := by
  constructor
  intro hx
  calc
    x = x * y := by rw[hx]
    _ = y := by apply Eq.refl
    _ ≤ y := by apply le_refl
  intro lx
  have g : x ≤ y → x = y := by apply h.incomp x y
  have h'' : x = y := by
    apply g
    apply lx
  have h''' : x * y = x := by
    rw[←h'']
    apply RightNormalBand.mul_idem
  apply h'''

end Anticadenas
end Antichains


section Principal
variable {α β : Type u} [RightNormalBand α]
#check SemilatticeInf

def SubProducto {α β : Type u} [PartialOrder α] [SemilatticeInf β] {f : α →o β }  : Set (β × α) :=
{x | x.1 ≤ f x.2}

lemma IsInSubProducto [PartialOrder α] [SemilatticeInf β] {f : α →o β }  : ∀ x y : (β × α) , y.1 ≤ f y.2 → x.1 ⊓ y.1 ≤  f y.2 := by
  intro x y yins
  calc
    x.1 ⊓ y.1 ≤ y.1 := by sorry
    _ ≤ f y.2 := by apply yins

def SubBand {α β : Type u} (P : PartialOrder α) (S : SemilatticeInf β) (f : α →o β ) (h : ∀(a : α), IsIso (InitialRestriction (α := α) (β := β) f a)) : SubProducto → SubProducto  → SubProducto  := fun x y =>
(x.1 ⊓ y.1, y.2)

instance {α β : Type u} (P : PartialOrder α) (S : SemilatticeInf β) (f : α →o β ) (h : ∀(a : α), IsIso (InitialRestriction (α := α) (β := β) f a)) : RightNormalBand (SubProducto P S f) where
mul := fun x y => ⟨(x.1 ⊓ y.1, y.2), ⟩

theorem NormalPosetsCharacterization {α : Type u} [P : PartialOrder α] : IsNormal P ↔ IsNormal' P := by
  constructor
  sorry
  sorry
