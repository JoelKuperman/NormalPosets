import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Lattice
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Partial
import Mathlib.Data.PFun
import Mathlib.Order.Category.PartOrd
import Mathlib.Algebra.Free
import Mathlib.GroupTheory.Subsemigroup.Basic
import Mathlib.GroupTheory.Subsemigroup.Operations
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Conjugate
import Mathlib.Logic.Function.Iterate



section Coerciones
variable {α β: Type u} {a b c d : α}


def injective (f : α → β) : Prop :=
∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂

def surjective (f : α → β) : Prop :=
∀ y, ∃ x, f x = y

def bijective (f : α → β) := injective f ∧ surjective f

lemma ExistInverse {f: α → β} {h : bijective f} : ∃ g, Function.LeftInverse g f ∧ Function.RightInverse g f := by
  apply Function.bijective_iff_has_inverse.1
  constructor
  intro x y
  apply h.1
  intro x
  apply h.2

lemma IsInverse {f: α → β}[Nonempty α] {h : bijective f} : Function.LeftInverse (Function.invFun f) f ∧ Function.RightInverse (Function.invFun f) f := by
  constructor
  apply Function.leftInverse_invFun
  intro x y
  apply h.1
  apply Function.rightInverse_invFun
  intro x
  apply h.2

def range (f : α → β) : Set β := --rango de una función
  { b | ∃ a, b = f a }
def Ordrange {α : Type u} {β : Type u} [Preorder α][Preorder β] (f : OrderHom α β) : Set β := --rango de un homomorfismo de orden
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

def OrdHomRange' [PartialOrder α] [PartialOrder β] (f : OrderHom α β)(p : Set α) (q : Set β) (c : Ordrange (OrdHomRestrict f p) ⊆ q): p → q := --Restringe el dominio y el codominio de un homomorfismo de orden
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

def IsIso {α β : Type u} [PartialOrder α] [PartialOrder β] (f : OrderHom α β) : Prop :=
  bijective f ∧   ∀ x y : α, f x ≤ f y  → x ≤ y

end Coerciones

section RightNormalBand
variable {α : Type u} [Nonempty α]

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

lemma InitIsDec' {α : Type u} [PartialOrder α] (a : α) : Decrec (Set.Iic a):= by exact fun x y h h' =>
  let_fun h'' := h;
  let_fun h''' := le_trans h' h'';
  h'''


lemma DecIsSub {α : Type u} [RightNormalBand α] (S : Set α) (h : Decrec S) : Closed S := by  --Prueba de que en una banda normal los decrecientes son cerrados
  intro x y
  have h' : x * y ≤ y := by apply por_is_leq
  intro _ h'''
  apply h
  apply h'''
  apply h'

end RightNormalBand
end RightNormalBand
section NormalPosets



def InitialSegment {α : Type u} [PartialOrder α] (a : α) : Set α := {b | b ≤ a}

def IsNormal {α : Type u} (_ : PartialOrder α) : Prop := --Existe una RNB \alpha tal que P es isomorfo al poset asociado a α
∃ (α': Type u),∃(_ : RightNormalBand α'), ∃(_:OrderIso α α'), True

theorem RestrictionInitial {α β: Type u} [PartialOrder α] [PartialOrder β] {f : α →o β} {b : α}: Ordrange (OrdHomRestrict f (Set.Iic  b)) ⊆ Set.Iic (f b) := by --Prueba de que la imagen de restricción de un homomorfismo al segmento inicial de b esta contenida en el segmento inicial de fb
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

def InitialRestriction {α β: Type u} [PartialOrder α] [PartialOrder β] (f : OrderHom α β)(a : α)  : Set.Iic a →o Set.Iic (f a) := --Toma una f y un a y devuelve f restringida al segmento inicial de a con codominio segmento inicial de (f a)
    OrdHomRange f (Set.Iic a) (Set.Iic (f a)) (RestrictionInitial)

end NormalPosets

section Subestructuras

-- variable {S : Type*} [RightNormalBand α] [SetLike  S α] [hA : MulMemClass S α] (s : S

def Closed [RightNormalBand α] (p : Set α) : Prop := ∀ x y : α, x ∈ p → y ∈ p → x * y ∈ p

variable {α : Type u} [RightNormalBand α]


--Restricción de un producto a un cerrado
def ProdRestrict {s : Set α} {h : Closed s} : s → s → s :=
fun x y =>
  ⟨x * y, by exact h (↑x) (↑y) x.property y.property⟩



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
    _ = ⟨x.1 * (y.1 * z.1), _⟩ := by simp_all[mul_assoc]
    _ = ProdRestrict (s:=s) (h:=h) x (ProdRestrict (s:=s) (h:=h) y z) := by apply Eq.refl

theorem RestricNorm {s : Set α} {h : Closed s} : ∀ x y z: s, ProdRestrict (s:=s) (h:=h) (ProdRestrict (s:=s) (h:=h) x y) z = ProdRestrict (s:=s) (h:=h) (ProdRestrict (s:=s) (h:=h) y x) z := by
  intro x y z
  calc
     ProdRestrict (s:=s) (h:=h) (ProdRestrict (s:=s) (h:=h) x y) z = ⟨x * y * z, _⟩ := by apply Eq.refl
    _ = ⟨y * x * z , _⟩ := by simp_all[RightNormalBand.mul_norm]
    _ = ProdRestrict (s:=s) (h:=h) (ProdRestrict (s:=s) (h:=h) y x) z := by apply Eq.refl

--Subestructura. Banda definida sobre un conjunto cerrado s.
instance SubBanda {s : Set α} {h : Closed s}: RightNormalBand s where
  mul := ProdRestrict (s := s) (h :=h)
  mul_assoc := RestricAsoc
  mul_norm :=  RestricNorm
  mul_idem := RestricIdem


end Subestructuras


section Productos
def MulProd [RightNormalBand α] [RightNormalBand β] : Mul (α × β) where
  mul := fun x y => ⟨x.1 * y.1, x.2 * y.2⟩

lemma MulProdAssoc [RightNormalBand α] [RightNormalBand β] : ∀ x y z : α × β, x * y * z = x * (y * z) := by
  intro x y z
  calc
    x * y * z = ⟨x.1 * y.1, x.2 * y.2⟩ * z := by apply Eq.refl
    _ = ⟨x.1 * y.1 * z.1, x.2 * y.2 * z.2⟩ := by apply Eq.refl
    _ = ⟨x.1 * (y.1 * z.1), x.2 * (y.2 * z.2)⟩ := by
      rw[←mul_assoc]
      rw[←mul_assoc]
    _ = x * ⟨y.1 * z.1, y.2 * z.2⟩:= by apply Eq.refl
    _ = x * (y * z) := by apply Eq.refl


instance BandProduct [A : RightNormalBand α] [B: RightNormalBand β] : RightNormalBand (α × β) where
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



theorem BandIsoisOrdIso {α β : Type u} [RightNormalBand α][RightNormalBand β] {f : MulHom α β} {h : bijective f.toFun}: IsIso (BandHomtoOrdHom f) := by exact
  { left := h,
    right := fun x y fxy =>
      let_fun g := Trans.trans (MulHom.map_mul' f x y) fxy;
      let_fun g'' :=
        And.left h (x * y) x
          (Eq.mpr (id (g ▸ Eq.refl (MulHom.toFun f (x * y) = MulHom.toFun f x))) (Eq.refl (MulHom.toFun f x)));
      g'' }
end Homomorfismos
section Congruencias

class Congruence (α : Type u) [RightNormalBand α] where

  r : α → α → Prop

  refl  : ∀ x, r x x

  symm  : ∀ {x y}, r x y → r y x

  trans : ∀ {x y z}, r x y → r y z → r x z

  cong : ∀ {x y z w}, r x y → r z w → r (x * z) (y * w)

--Las siguientes dos definiciones son para probar CongSound, la recíproca de QuotSound

def Cociente' {α : Type u} [RightNormalBand α] {h : Congruence α} : Setoid α where
  r := h.r
  iseqv := by exact
    { refl := Congruence.refl, symm := fun {x y} => Congruence.symm, trans := fun {x y z} => Congruence.trans }

def Cociente'' {α : Type u} [RightNormalBand α] {h : Congruence α} : HasEquiv α where
  Equiv := h.r
theorem QuotForm {α : Type u} [RightNormalBand α] {h : Congruence α} : ∀ x : Quot h.r, ∃x' : α, x = Quot.mk h.r x' := by
  apply Quot.ind
  intro a
  have h' : Quot.mk h.r a = Quot.mk h.r a := by apply Eq.refl
  apply Exists.intro a h'

lemma CongSound{α : Type u} [RightNormalBand α] {h : Congruence α} : ∀ x y : α, Quot.mk h.r x = Quot.mk h.r y → h.r x y := by
  intro x y xry
  have h' : Cociente''.Equiv x y:= by
    have h'' : Quotient.mk Cociente' x = Quotient.mk Cociente' y := by
      calc
        Quotient.mk Cociente' x = Quot.mk h.r x := by rfl
        _ = Quot.mk h.r y := by apply xry
        _ = Quotient.mk Cociente' y := by rfl
    apply Quotient.exact (s:=Cociente')
    apply h''
  exact h'

def ProjCann' {α : Type u} [RightNormalBand α] {h : Congruence α} : α → Quot h.r := fun a => Quot.mk h.r a



theorem ProjCongr'' {α : Type u} [RightNormalBand α] {h : Congruence α} : ∀ x y z : α,  h.r y z → Quot.mk h.r (x * y) = Quot.mk h.r (x * z) := by
intro x y z yrz
have h' : h.r (x * y) (x *z) := by exact Congruence.cong (Congruence.refl x) yrz
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



def ProjCann {α : Type u} [RightNormalBand α] {h : Congruence α} : MulHom α (Quot h.r) where --La proyección canónica como homomorfismo de álgebra
  toFun := ProjCann'
  map_mul' := by
    intro x y
    calc
      ProjCann' (x * y) = Quot.mk h.r (x * y) := by apply Eq.refl
      _ = (Quot.mk h.r x) * (Quot.mk h.r y) := by apply Eq.refl


--La proyección canónica como homomorfismo de orden
def OrderProj {α : Type u} [RightNormalBand α] {h : Congruence α} : α →o (Quot h.r) :=
  BandHomtoOrdHom ProjCann

--La relación de la congruencia de proyecciones
def Project  [RightNormalBand α] (a b : α) := a * b = b ∧ b * a = a

--La rel anterior es reflexiva
theorem ProjectRefl [RightNormalBand α]  {a : α} : Project a a := by
  have h' : a * a = a := by apply RightNormalBand.mul_idem
  have h'' : a * a = a ∧ a * a = a := by
    rename_i inst
    simp_all only [and_self]
  apply h''

--La rel anterior es simétrica
theorem ProjectSymm [RightNormalBand α]  {a b: α} : Project a b → Project b a := by
  intro x
  constructor
  apply x.right
  apply x.left

--La rel anterior es reflexiva
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


instance ProjectCong (A : RightNormalBand α) : Congruence α where
  r := Project
  refl := by exact fun x => ProjectRefl
  symm := by exact fun {x y1} => ProjectSymm
  trans := by exact fun {x y z} => ProjectTrans
  cong := by exact fun {x y z w} => ProjectCongr


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

theorem RestrictProjectIsIso {A : RightNormalBand α} (a : α) : IsIso (InitialRestriction (OrderProj (h := ProjectCong A)) a)  := by
  constructor
  constructor
  intro x y fxy
  have g : Quot.mk Project x.1 = Quot.mk Project y.1 := by
    calc
      Quot.mk Project x.1 = OrderProj x.1 := by apply Eq.refl
      _ = (InitialRestriction (OrderProj (h := ProjectCong A)) a) x := by apply Eq.refl
      _ = (InitialRestriction (OrderProj (h := ProjectCong A)) a) y := by simp_all[fxy]
      _ = OrderProj y.1 := by apply Eq.refl
      _ = Quot.mk Project y.1 := by apply Eq.refl
  have g' : Project x.1 y.1 := by
    apply CongSound
    apply g
  have g'' : x.1 ≤ a := by apply x.2
  have j : x.1 * a = x.1 := by
    apply g''

  have g''' : y.1 ≤ a := by apply y.2
  have h' : x.1 = y.1 := by
    calc
      x.1 = x.1 * a := by simp_all[g'']
      _ = y.1 * x.1 * a := by rw[g'.right]
      _ = x.1 * y.1 * a := by apply RightNormalBand.mul_norm
      _ = y.1 * a := by rw[g'.left]
      _ = y.1 := by apply g'''
  simp_all[h']
  exact SetCoe.ext h'
  intro x
  have w : ∃ x' : α, x = Quot.mk Project x' := by apply QuotForm
  rcases w with ⟨x', hx⟩
  have w' : x' * a ∈ Set.Iic a := by simp
  have l : x.1 * Quot.mk Project a = x.1 := by
    apply x.2
  have r : QuotBand.mul (Quot.mk Project x') (Quot.mk Project a) = Quot.mk Project x' := by
      calc
        QuotBand.mul (Quot.mk Project x') (Quot.mk Project a) = QuotBand.mul x (Quot.mk Project a) := by rw[hx]
        _ = x := by apply l
        _ = Quot.mk Project x' := by rw[←hx]
  have w'' : InitialRestriction (OrderProj (h := ProjectCong A)) a ⟨x' * a, w'⟩ = x.1 := by
    calc
      InitialRestriction (OrderProj (h := ProjectCong A)) a ⟨x' * a, w'⟩ = OrderProj (x'* a) := by apply Eq.refl
      _ = Quot.mk Project (x'* a) := by apply Eq.refl
      _ = QuotBand.mul (Quot.mk Project x') (Quot.mk Project a) := by apply Eq.refl
      _ = Quot.mk Project x' := by apply r
      _ = x := by simp_all[hx]
  have w''' : InitialRestriction (OrderProj (h := ProjectCong A)) a ⟨x' * a, w'⟩ = x := by
    exact SetCoe.ext w''

  simp_all[w''']
  exact BEx.intro (x' * a) w' w'''
  intro x y xley
  have r' : Project (y.1 * x.1) x.1 := by
    apply CongSound
    calc
      Quot.mk Project (y.1 * x.1) = Quot.mk Project (x.1* y.1) := by
        apply Quot.sound
        apply ProductProject
      Quot.mk Project (x.1* y.1) = QuotBand.mul (Quot.mk Project x.1) (Quot.mk Project y.1) := by apply Eq.refl
      _ = Quot.mk Project x.1 := by apply xley
  have r'' : y.1 * x.1 = x.1 := by
    calc
      y.1 * x.1 = y.1 * (x.1 * x.1) := by rw[RightNormalBand.mul_idem]
      _ = y.1 * x.1 * x.1 := by rw[←mul_assoc]
      _ = x.1 := by apply r'.left

  have q : y.1 * a  = y.1 := by apply y.2
  have q' : x.1 * a  = x.1 := by apply x.2

  calc
    x.1 * y.1 = x.1 * (y.1 * a) := by rw[q]
    _ = x.1 * y.1 * a := by rw[mul_assoc]
    _ = y.1 * x.1 * a := by rw[RightNormalBand.mul_norm]
    _ = x.1 * a := by rw[r'']
    _ = x.1 := by rw[q']


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

instance QuotSemilattice (A : RightNormalBand α) : SemilatticeInf (Quot Project (α:= α)) where
inf := QuotProd
le := QuotBand.leq
le_refl := QuotBand.refl_le
le_trans := QuotBand.trans_le
le_antisymm := QuotBand.antisymm_le
inf_le_left := QuotInfLeft
inf_le_right := QuotBand.por_is_leq
le_inf := QuotInf

theorem ExistsInitIso [RightNormalBand α] : ∃ α' : Type u, ∃ S : SemilatticeInf α', ∃ f : α →o α', ∀ a : α, IsIso (InitialRestriction f a) := by
  refine nonempty_subtype.mp ?_
  use Quot Project (α := α)
  use QuotSemilattice _
  use (OrderProj (h := ProjectCong _))
  apply RestrictProjectIsIso
end Congruencias
def AntichainProd {α : Type u}: Mul α  where
  mul := fun _ y => y

 theorem ACProdAssoc {α : Type u} :∀ a b c : α,  AntichainProd.mul (AntichainProd.mul a b) c = AntichainProd.mul a (AntichainProd.mul b c) := by
  intro a b c
  calc
    AntichainProd.mul (AntichainProd.mul a b) c =  AntichainProd.mul b c := by
      apply Eq.refl
   _ = AntichainProd.mul a (AntichainProd.mul b c) := by
      apply Eq.refl

   theorem ACProdRefl {α : Type u} :∀ a : α, AntichainProd.mul a a = a := by apply Eq.refl

   theorem ACProdNorm {α : Type u}: ∀ a b c : α, AntichainProd.mul (AntichainProd.mul a b) c = AntichainProd.mul (AntichainProd.mul b a) c := by
    intro a b c
    calc
        AntichainProd.mul (AntichainProd.mul a b) c = c := by apply Eq.refl
        _ = AntichainProd.mul (AntichainProd.mul b a) c := by apply Eq.refl


@[default_instance 1]
instance AntichainNormal {α : Type u} [PartialOrder α] : RightNormalBand α where
  mul := AntichainProd.mul
  mul_assoc := ACProdAssoc
  mul_norm := ACProdNorm
  mul_idem := ACProdRefl

section Semilattices
variable {α : Type u} [SemilatticeInf α]


theorem SLNorm : ∀ a b c : α, a ⊓ b ⊓ c = b ⊓ a ⊓ c := by
  intro a b c
  simp [inf_comm]

@[default_instance 2000]
instance SemilatticeNormal [S: SemilatticeInf α] : RightNormalBand α where
  mul := Inf.inf
  mul_assoc := by apply inf_assoc
  mul_norm := SLNorm
  mul_idem := by apply inf_idem

end Semilattices


section Principal
variable {α β : Type u} [Nonempty α] [Nonempty β]

--Definición necesaria para hacer andar varias cosas. Toma un par b ≤ c y devuelve a b como elemento de c↓
def MapTo {α : Type u} [PartialOrder α] (b c: α) {h' : b ≤ c } : Set.Iic c := ⟨b, h'⟩

--Si dos elementos estan por debajo de un cierto c y tienen la misma imagen mediante una funcion que cumple h, entonces son iguales
theorem InitInject [PartialOrder α] [PartialOrder β] {f: α →o β} {h : ∀a : α, IsIso (InitialRestriction f a)} :∀ a b, (∃c, a ≤ c ∧ b≤ c ∧ f a= f b) → a = b   := by
    intro s t ec
    rcases ec with ⟨c, lc⟩
    have w : (InitialRestriction f c ⟨s,by simp_all[lc]⟩).1 = (InitialRestriction f c ⟨t,by simp_all[lc]⟩).1 := by
      calc
        (InitialRestriction f c ⟨s,by simp_all[lc]⟩).1 = f s := by apply Eq.refl
        _ = f t := by simp_all[lc]
        _ = (InitialRestriction f c ⟨t,by simp_all[lc]⟩).1 := by apply Eq.refl

    have w' : (InitialRestriction f c ⟨s,by simp_all[lc]⟩) = (InitialRestriction f c ⟨t,by simp_all[lc]⟩) := by
      exact SetCoe.ext w
    have w'' : MapTo s c = MapTo t c := by
      calc
        MapTo s c = ⟨s, by simp_all[lc]⟩ := by apply Eq.refl
        _ = ⟨t, by simp_all[lc]⟩ := by
          apply (h c).left.left
          apply w'
        _ = MapTo t c := by apply Eq.refl
    calc
      s = (MapTo s c).1 := by
        exact rfl
      _ = (MapTo t c).1 := by
        exact congrArg Subtype.val w''
      _ = t := by exact rfl


-- Componer con un isomorfismo preserva la propiedad que queremos-
theorem IsoComp' {α β γ: Type u} [PartialOrder α][PartialOrder β] [PartialOrder γ] {f : α →o γ} {g : β →o α} {h : ∀(a : α), IsIso (InitialRestriction (α := α) (β := γ) f a)}{h' : IsIso g} : ∀(a : β), IsIso (InitialRestriction (α := β) (β := γ) (OrderHom.comp f g) a) := by
  intro a
  have j : IsIso (InitialRestriction f  (g a)) := by apply h
  constructor
  constructor
  intro x y fxy
  have k₁ : g x ≤ g a := by
    apply g.monotone'
    apply x.2
  have k₂ : g y ≤ g a := by
    apply g.monotone'
    apply y.2

  have k :  InitialRestriction f (g a) ⟨g x, k₁⟩ =InitialRestriction f (g a) ⟨g y, k₂⟩  := by
    calc
      InitialRestriction f (g a) ⟨g x, k₁⟩  = (InitialRestriction (OrderHom.comp f g) a) x := by apply Eq.refl
      _ = (InitialRestriction (OrderHom.comp f g) a) y := by simp_all[fxy]
      _ = InitialRestriction f (g a) ⟨g y, k₂⟩ := by apply Eq.refl
  have k' : f (g x) = f (g y) := by
    calc
      f (g x) = InitialRestriction f (g a) ⟨g x, k₁⟩ := by apply Eq.refl
      _ = InitialRestriction f (g a) ⟨g y, k₂⟩ := by simp_all[k]
      _ = f (g y) := by apply Eq.refl

  have th : ∀s t : α, s ≤ g a → t ≤ g a → f s = f t → s = t := by
    intro s t gs gt st
    have w : InitialRestriction f (g a) ⟨s,gs⟩ = InitialRestriction f (g a) ⟨t, gt⟩ := by
     exact SetCoe.ext st

    have w' : MapTo s (g a) = MapTo t (g a) := by
      calc
        MapTo s (g a) = ⟨s, gs⟩ := by apply Eq.refl
        _ = ⟨t, gt⟩ := by
          apply j.left.left
          apply w
        _ = MapTo t (g a) := by apply Eq.refl
    calc
      s = (MapTo s (g a)).1 := by
        exact rfl
      _ = (MapTo t (g a)).1 := by
        exact congrArg Subtype.val w'
      _ = t := by exact rfl
  have t' : g x = g y := by
    apply th
    apply k₁
    apply k₂
    apply k'
  exact SetCoe.ext (h'.left.left (↑x) (↑y) (t'))
  --Surjectividad
  intro x
  have k : ∃ x', InitialRestriction f (g a) x' = x := by
    apply j.left.right
  rcases k with ⟨x', hx⟩
  have k' : ∃b', g b' = x' := by apply h'.left.right
  rcases k' with ⟨b, hb⟩
  have blea : b≤a := by
    apply h'.right
    simp_all[hb]
    apply x'.2

  have w : ((InitialRestriction (OrderHom.comp f g) a) ⟨b, blea⟩).1 = x.1 := by
    calc
      ((InitialRestriction (OrderHom.comp f g) a) ⟨b, blea⟩).1 = f (g b) := by apply Eq.refl
      _ = f x' := by simp_all[hb]
      _ = InitialRestriction f (g a) x' := by apply Eq.refl
      _ = x := by simp_all[hx]
  have w' : (InitialRestriction (OrderHom.comp f g) a) ⟨b, blea⟩ = x := by
    exact SetCoe.ext w
  exact Exists.intro { val := b, property := blea } w'

  --Inversa preserva orden
  intro x y xley
  have k₁ : g x ≤ g a := by
    apply g.monotone'
    apply x.2
  have k₂ : g y ≤ g a := by
    apply g.monotone'
    apply y.2

  have k  :(InitialRestriction (OrderHom.comp f g) a) y = InitialRestriction f (g a) ⟨g y, k₂⟩ := by
    exact rfl
  have k'  :(InitialRestriction (OrderHom.comp f g) a) x = InitialRestriction f (g a) ⟨g x, k₁⟩ := by
    exact rfl
  have r : MapTo (g x) (g a) ≤ MapTo (g y) (g a) := by
    apply j.right
    calc
      InitialRestriction f (g a) (MapTo (g x) (g a)) = InitialRestriction f (g a) ⟨g x, k₁⟩ := by apply Eq.refl
      _ = (InitialRestriction (OrderHom.comp f g) a) x  := by apply k'
      _ ≤  (InitialRestriction (OrderHom.comp f g) a) y := by apply xley
      _ = InitialRestriction f (g a) ⟨g y, k₂⟩ := by apply k
  have r' : g x ≤ g y := by exact r
  apply h'.right
  apply r'

--Convierte un isomorfismo de orden en un homomorfismo
def IsotoOrderHom  {α β: Type u} [PartialOrder α] [PartialOrder β] (f : α ≃o β) : α →o β where
toFun := f.toFun
monotone' := by
  intro a b aleb
  simp
  apply aleb

--Para todo isomorfismo f, IsIso f
lemma IsoisIso {α : Type u} [P : PartialOrder α] [PartialOrder β] {f : α ≃o β} : IsIso (IsotoOrderHom f) := by
  constructor
  constructor
  intro x y fxy
  have h' : f x = f y := by
    calc
      f x = IsotoOrderHom f x := by apply Eq.refl
      _ = IsotoOrderHom f y := by apply fxy
      _ = f y := by apply Eq.refl
  simp_all[h']
  intro x
  have h' : IsotoOrderHom f (f.invFun x) = x := by
    calc
      IsotoOrderHom f (f.invFun x) = f (f.invFun x) := by apply Eq.refl
      _ = x := by simp
  exact Exists.intro (Equiv.invFun f.toEquiv x) h'
  intro x y xley
  have h' : f x≤f y:= by
    calc
      f x = IsotoOrderHom f x := by apply Eq.refl
      _ ≤ IsotoOrderHom f y  := by simp_all[xley]
      _ = f y := by apply Eq.refl
  simp_all



--Un subconjunto del producto anterior dado por una propiedad respecto a una f
def SubProducto {α β : Type u} [PartialOrder α] [SemilatticeInf β] (f : α →o β )  : Set (β × α) :=
  {x | x.1 ≤ f x.2}



--Producto de un semirretículo por una anticadena
@[default_instance 200]
instance ProductoNormal {α β : Type u} [PartialOrder α] [S : SemilatticeInf β]  : RightNormalBand (β × α) :=
  BandProduct (A := SemilatticeNormal (S := S)) (B := AntichainNormal (α := α))

lemma ClosedSubProducto {α β : Type u} [P : PartialOrder α] [S : SemilatticeInf β] {f : α →o β}  : Closed (SubProducto f):= by
  intro x y _ yis
  have h : (x * y).1 ≤ f (x * y).2 := by
    calc
      (x * y).1 = x.1 * y.1 := by apply Eq.refl
      _ ≤ y.1 := by
        apply RightNormalBand.por_is_leq
      _ ≤ f y.2 := by apply yis
      _ = f (x.2 * y.2) := by apply rfl
      _ = f (x * y).2 := by apply Eq.refl
  apply h




--Definicion de una banda sobre este subconjunto
@[default_instance 200]
instance SubProductoNormal {α β : Type u} [PartialOrder α] [SemilatticeInf β] {f : α →o β } : RightNormalBand (SubProducto f) :=
  SubBanda (s:= SubProducto f) (h:= ClosedSubProducto)



--Defino una función cuyo kernel resultará congruencia
noncomputable def Proy {α β : Type u} [PartialOrder α] [SemilatticeInf β] {f : α →o β } (x : SubProducto f) : α :=
  (Function.invFun (InitialRestriction f x.1.2) ⟨x.1.1, x.2⟩).1

--El kernel
noncomputable def KerProy {α β : Type u} [PartialOrder α] [SemilatticeInf β] {f : α →o β} (x y : SubProducto f) : Prop := Proy x = Proy y

--Reflexividad
lemma KerProyRefl {α β : Type u} [PartialOrder α] [SemilatticeInf β] {f : α →o β} : ∀ x : SubProducto f, KerProy x x := by
  intro x
  apply Eq.refl

--Simetría
lemma KerProySymm {α β : Type u} [PartialOrder α] [SemilatticeInf β] {f : α →o β} : ∀ x y: SubProducto f, KerProy x y → KerProy y x := by
  intro x y kxy
  have k' : Proy y = Proy x := by
   rw[kxy]
  apply k'

--Transitividad
lemma KerProyTrans {α β : Type u} [PartialOrder α] [SemilatticeInf β] {f : α →o β} : ∀ x y z: SubProducto f, KerProy x y → KerProy y z → KerProy x z := by
  intro x y z xry yrz
  have h' : Proy x = Proy z := by
    calc
      Proy x = Proy y := by rw[xry]
      _ = Proy z := by rw[yrz]
  apply h'

--Respeta producto
lemma KerProyCong {α β : Type u} {P : PartialOrder α} {S : SemilatticeInf β} {f : α →o β} {hf : ∀ a : α, IsIso (InitialRestriction f a)} : ∀ x y z w: SubProducto f, KerProy x y → KerProy z w → KerProy (x * z) (y * w) := by
  intro x y z w xry zrw
  have h' :  (Function.invFun (InitialRestriction f x.1.2) ⟨x.1.1, x.2⟩).1 =  (Function.invFun (InitialRestriction f y.1.2) ⟨y.1.1, y.2⟩).1 := by
   apply xry
  have g' : (Function.invFun (InitialRestriction f z.1.2) ⟨z.1.1, z.2⟩).1 =  (Function.invFun (InitialRestriction f w.1.2) ⟨w.1.1, w.2⟩).1 := by
   apply zrw
  have h'' : x.1.1 = y.1.1 := by
    calc
      x.1.1 =(InitialRestriction f x.1.2 (Function.invFun (InitialRestriction f x.1.2) ⟨x.1.1,x.2⟩)).1   := by
        rw[(IsInverse (f:= InitialRestriction f x.1.2) (h:= (hf x.1.2).1)).right]
      _ = (f (Function.invFun (InitialRestriction f x.1.2) ⟨x.1.1,x.2⟩).1) := by apply Eq.refl
      _ = (f (Function.invFun (InitialRestriction f y.1.2) ⟨y.1.1,y.2⟩).1) := by rw[h']
      _ = (InitialRestriction f y.1.2 (Function.invFun (InitialRestriction f y.1.2) ⟨y.1.1,y.2⟩)).1 := by
        apply Eq.refl
      _ = y.1.1 := by rw[(IsInverse (f:= InitialRestriction f y.1.2) (h:= (hf y.1.2).1)).right]

  have h''' : z.1.1 = w.1.1 := by
      calc
      z.1.1 =(InitialRestriction f z.1.2 (Function.invFun (InitialRestriction f z.1.2) ⟨z.1.1,z.2⟩)).1   := by
        rw[(IsInverse (f:= InitialRestriction f z.1.2) (h:= (hf z.1.2).1)).right]
      _ = (f (Function.invFun (InitialRestriction f z.1.2) ⟨z.1.1,z.2⟩).1) := by apply Eq.refl
      _ = (f (Function.invFun (InitialRestriction f w.1.2) ⟨w.1.1,w.2⟩).1) := by rw[g']
      _ = (InitialRestriction f w.1.2 (Function.invFun (InitialRestriction f w.1.2) ⟨w.1.1,w.2⟩)).1 := by
        apply Eq.refl
      _ = w.1.1 := by rw[(IsInverse (f:= InitialRestriction f w.1.2) (h:= (hf w.1.2).1)).right]



  have k₁ : x.1.1 * z.1.1 ≤ f z.1.2 := by
    calc
      x.1.1 * z.1.1 ≤ z.1.1 := by apply RightNormalBand.por_is_leq
      _ ≤ f z.1.2 := by apply z.2
  have k₂ : (y.1.1 * w.1.1) ≤ f w.1.2 := by
    calc
     y.1.1 * w.1.1 ≤  w.1.1 := by apply RightNormalBand.por_is_leq
      _ ≤ f w.1.2 := by apply w.2

  have k₄ : x.1.1 * z.1.1 = (x * z).1.1 := by
    calc
      x.1.1 * z.1.1 = (x.1 * z.1).1 := by apply Eq.refl
      _ = ((x * z).1).1 := by apply Eq.refl

  have k : Proy (x * z) = (Function.invFun (InitialRestriction f z.1.2) ⟨(x.1.1 * z.1.1), k₁⟩).1 := by
    calc
       Proy (x * z) = (Function.invFun (InitialRestriction f (x * z).1.2) ⟨(x * z).1.1, (x*z).2⟩).1 := by apply Eq.refl
       _ = ((Function.invFun (InitialRestriction f z.1.2)) ⟨(x.1.1 * z.1.1), k₁⟩).1 := by
        apply InitInject (β:= β) (h:=hf)
        have w' : (Function.invFun (InitialRestriction f z.1.2) ⟨x.1.1 * z.1.1, k₁⟩).1 ≤ z.1.2 := by
         apply (Function.invFun (InitialRestriction f  z.1.2) ⟨x.1.1 * z.1.1, k₁⟩).2

        have w'' : ((Function.invFun (InitialRestriction f z.1.2)) ⟨(x.1.1 * z.1.1), k₁⟩).1 ≤ z.1.2 := by apply ((Function.invFun (InitialRestriction f z.1.2)) ⟨(x.1.1 * z.1.1), k₁⟩).2
        have w''' : f ((Function.invFun (InitialRestriction f (x * z).1.2) ⟨(x * z).1.1, (x*z).2⟩).1) = f (((Function.invFun (InitialRestriction f z.1.2)) ⟨(x.1.1 * z.1.1), k₁⟩).1) := by
          calc
            f ((Function.invFun (InitialRestriction f (x * z).1.2) ⟨(x * z).1.1, (x*z).2⟩).1) = ((InitialRestriction f (x * z).1.2) ((Function.invFun (InitialRestriction f (x * z).1.2) ⟨(x * z).1.1, (x*z).2⟩))).1 :=
              by exact rfl
            _ = (x * z).1.1 := by rw[(IsInverse (f:= InitialRestriction f (x * z).1.2) (h:= (hf (x * z).1.2).1)).right]
            _ = ((InitialRestriction f z.1.2) ((Function.invFun (InitialRestriction f  z.1.2) ⟨(x.1.1 * z.1.1), k₁⟩))).1 := by
                rw[(IsInverse (f:= InitialRestriction f z.1.2) (h:= (hf z.1.2).1)).right]
                exact k₄
            _ = f ((Function.invFun (InitialRestriction f  z.1.2) ⟨(x.1.1 * z.1.1), k₁⟩).1) := by rfl
        have w : (Function.invFun (InitialRestriction f (x * z).1.2) ⟨(x.1.1 * z.1.1), k₁⟩).1 ≤ z.1.2 ∧ ((Function.invFun (InitialRestriction f z.1.2)) ⟨(x.1.1 * z.1.1), k₁⟩).1 ≤ z.1.2 ∧ f ((Function.invFun (InitialRestriction f (x * z).1.2) ⟨(x.1.1 * z.1.1), (x*z).2⟩).1) = f (((Function.invFun (InitialRestriction f z.1.2)) ⟨(x.1.1 * z.1.1), k₁⟩).1) := by
          constructor
          apply w'
          constructor
          apply w''
          apply w'''
        exact Exists.intro z.1.2 w

  have k' : Proy (y * w) = (Function.invFun (InitialRestriction f w.1.2) ⟨(y.1.1 * w.1.1), k₂⟩).1 := by
    calc
       Proy (y * w) = (Function.invFun (InitialRestriction f (y * w).1.2) ⟨(y * w).1.1, (y*w).2⟩).1 := by apply Eq.refl
       _ = (Function.invFun (InitialRestriction f (y * w).1.2) ⟨(y.1.1 * w.1.1), (y*w).2⟩).1 := by rfl
       _ = ((Function.invFun (InitialRestriction f w.1.2)) ⟨(y.1.1 * w.1.1), k₂⟩).1 := by
        apply InitInject (β:= β) (h:=hf)
        have w' : (Function.invFun (InitialRestriction f (y * w).1.2) ⟨(y.1.1 * w.1.1), (y*w).2⟩).1 ≤ w.1.2 := by
          calc
            (Function.invFun (InitialRestriction f (y * w).1.2) ⟨(y.1.1 * w.1.1), (y*w).2⟩).1 ≤ (y*w).1.2 := by apply (Function.invFun (InitialRestriction f (y * w).1.2) ⟨(y.1.1 * w.1.1), (y*w).2⟩).2
            _ = y.1.2 * w.1.2 := by rfl
            _ = w.1.2 := by rfl
        have w'' : ((Function.invFun (InitialRestriction f w.1.2)) ⟨(y.1.1 * w.1.1), k₂⟩).1 ≤ w.1.2 := by apply ((Function.invFun (InitialRestriction f w.1.2)) ⟨(y.1.1 * w.1.1), k₂⟩).2
        have w''' : f ((Function.invFun (InitialRestriction f (y * w).1.2) ⟨(y.1.1 * w.1.1), (y*w).2⟩).1) = f (((Function.invFun (InitialRestriction f w.1.2)) ⟨(y.1.1 * w.1.1), k₂⟩).1) := by
          calc
            f ((Function.invFun (InitialRestriction f (y * w).1.2) ⟨(y.1.1 * w.1.1), (y*w).2⟩).1) = ((InitialRestriction f (y * w).1.2) ((Function.invFun (InitialRestriction f (y * w).1.2) ⟨(y.1.1 * w.1.1), (y*w).2⟩))).1 :=
              by exact rfl
            _ = y.1.1 * w.1.1 := by rw[(IsInverse (f:= InitialRestriction f (y * w).1.2) (h:= (hf (y * w).1.2).1)).right]
            _ = ((InitialRestriction f w.1.2) ((Function.invFun (InitialRestriction f  w.1.2) ⟨(y.1.1 * w.1.1), k₂⟩))).1 := by
                rw[(IsInverse (f:= InitialRestriction f w.1.2) (h:= (hf w.1.2).1)).right]
            _ = f ((Function.invFun (InitialRestriction f  w.1.2) ⟨(y.1.1 * w.1.1), k₂⟩).1) := by rfl
        have wz : (Function.invFun (InitialRestriction f (y * w).1.2) ⟨(y.1.1 * w.1.1), (y*w).2⟩).1 ≤ w.1.2 ∧ ((Function.invFun (InitialRestriction f w.1.2)) ⟨(y.1.1 * w.1.1), k₂⟩).1 ≤ w.1.2 ∧ f ((Function.invFun (InitialRestriction f (y * w).1.2) ⟨(y.1.1 * w.1.1), (y*w).2⟩).1) = f (((Function.invFun (InitialRestriction f w.1.2)) ⟨(y.1.1 * w.1.1), k₂⟩).1) := by
          constructor
          apply w'
          constructor
          apply w''
          apply w'''
        exact Exists.intro w.1.2 wz

  have j : Proy (x * z) = Proy (y * w) := by
    apply InitInject (β:= β) (h:=hf)
    have s: Proy (x * z) ≤ z.1.2 := by
      calc
         Proy (x * z) = (Function.invFun (InitialRestriction f z.1.2) ⟨(x.1.1 * z.1.1), k₁⟩).1 := by apply k
         _ ≤ z.1.2 := by apply (Function.invFun (InitialRestriction f z.1.2) ⟨(x.1.1 * z.1.1), k₁⟩).2
    have s': Proy (y * w) ≤ z.1.2 := by
      calc
        Proy (y * w) = (Function.invFun (InitialRestriction f w.1.2) ⟨(y.1.1 * w.1.1), k₂⟩).1 := by apply k'
        _ ≤ (Function.invFun (InitialRestriction f w.1.2) ⟨(w.1.1), w.2⟩).1  := by
          apply (hf w.1.2).2
          calc
            f ((Function.invFun (InitialRestriction f w.1.2) ⟨(y.1.1 * w.1.1), k₂⟩).1) = ((InitialRestriction f w.1.2) ((Function.invFun (InitialRestriction f w.1.2) ⟨(y.1.1 * w.1.1), k₂⟩))).1 := by rfl
            _ = y.1.1 * w.1.1 := by rw[(IsInverse (f:= InitialRestriction f  w.1.2) (h:= (hf w.1.2).1)).right]
            _ ≤ w.1.1 := by apply RightNormalBand.por_is_leq
            _ = ((InitialRestriction f w.1.2) ((Function.invFun (InitialRestriction f w.1.2) ⟨(w.1.1), w.2⟩))).1 := by rw[(IsInverse (f:= InitialRestriction f  w.1.2) (h:= (hf w.1.2).1)).right]
            _ = f ((Function.invFun (InitialRestriction f w.1.2) ⟨(w.1.1), w.2⟩).1) := by rfl
        _ = (Function.invFun (InitialRestriction f z.1.2) ⟨(z.1.1), z.2⟩).1 := by rw[g']
        _ ≤ z.1.2 := by apply (Function.invFun (InitialRestriction f z.1.2) ⟨(z.1.1), z.2⟩).2
    have s'' : f (Proy (x*z) ) = f ( Proy (y*w) ) := by
      calc
        f (Proy (x * z)) = f ((Function.invFun (InitialRestriction f z.1.2) ⟨(x.1.1 * z.1.1), k₁⟩).1) := by rw[k]
        _ = ((InitialRestriction f z.1.2) ((Function.invFun (InitialRestriction f z.1.2) ⟨(x.1.1 * z.1.1), k₁⟩))).1 := by rfl
        _ = x.1.1*z.1.1 := by rw[(IsInverse (f:= InitialRestriction f  z.1.2) (h:= (hf z.1.2).1)).right]
        _ = y.1.1 * w.1.1 := by
          rw[h'']
          rw[h''']
        _ = ((InitialRestriction f w.1.2) ((Function.invFun (InitialRestriction f w.1.2) ⟨(y.1.1 * w.1.1), k₂ ⟩))).1 := by rw[(IsInverse (f:= InitialRestriction f  w.1.2) (h:= (hf w.1.2).1)).right]
        _ = f ((Function.invFun (InitialRestriction f w.1.2) ⟨(y.1.1 * w.1.1), k₂⟩).1) := by rfl
        _ = f (Proy (y * w)) := by rw[k']
    have s''' : Proy (x * z) ≤ z.1.2 ∧ Proy (y * w) ≤ z.1.2 ∧ f (Proy (x*z) ) = f ( Proy (y*w) ) := by
      constructor
      apply s
      constructor
      apply s'
      apply s''
    exact Exists.intro z.1.2 s'''
  exact j



--Defino una banda sobre el cociente por el kernel
instance NormalQuot {α β : Type u} {P : PartialOrder α} {S : SemilatticeInf β} {f : α →o β} {hf : ∀ a : α, IsIso (InitialRestriction f a)} : Congruence (SubProducto f) where
  r := KerProy
  refl := by exact fun x => KerProyRefl x
  symm := by exact fun {x y} kxy => KerProySymm x y kxy
  trans := by exact fun {x y z} kxy kyz => KerProyTrans x y z kxy kyz
  cong := by exact fun {x y z w} kxy kzw => KerProyCong (hf :=hf) x y z w kxy kzw

--Prueba de pertenencia a la subestructura que usare bastante
lemma IsInSubProd {α β : Type u} {P : PartialOrder α} {S : SemilatticeInf β} {f : α →o β} : ∀ x : α, (f x, x) ∈ (SubProducto f) := by
  intro x
  have h' : f x ≤ f x := by apply Preorder.le_refl
  exact h'

--Defino una función. La misma resultará un isomorfismo del poset P que viene apareciendo en las definiciones en el cociente que acabamos de definir
def IsNormalHom'  {α β : Type u} {P : PartialOrder α} {S : SemilatticeInf β} {f : α →o β} {hf : ∀ a : α, IsIso (InitialRestriction f a)} : α → Quot (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r := fun x =>
  Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r ⟨(f x, x), by apply IsInSubProd x⟩

--Lo defino como homomorfismo de orden(al pedo)
def IsNormalHom  {α β : Type u} {P : PartialOrder α} {S : SemilatticeInf β} {f : α →o β} {hf : ∀ a : α, IsIso (InitialRestriction f a)} : α →o Quot (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r where
  toFun := IsNormalHom'
  monotone' := by
    intro x y xley
    have k₁ : (f x * f y, y) ∈ (SubProducto f) := by
      have h' : f x * f y ≤ f y := by apply RightNormalBand.por_is_leq
      apply h'
    have k₂ : (f x, y) ∈ (SubProducto f) := by
      have h' : f x ≤ f y := by
        apply f.monotone'
        apply xley
      apply h'
    have h'' : Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r (⟨(f x , y), k₂⟩) = Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r (⟨(f x , x), IsInSubProd x⟩) := by
      have k : KerProy (⟨(f x , y), k₂⟩) (⟨(f x , x), IsInSubProd (P := P) (S:= S) (f := f) x⟩) := by
        have k' : Proy (⟨(f x , y), k₂⟩) = Proy (⟨(f x , x), IsInSubProd (P := P) (S:= S) (f := f) x⟩) := by
          calc
            Proy (⟨(f x , y), k₂⟩) = (Function.invFun (InitialRestriction f y) ⟨f x, k₂⟩).1 := by rfl
            _ = (Function.invFun (InitialRestriction f x) ⟨f x, IsInSubProd x⟩).1 := by
              apply InitInject (β:= β) (h:=hf)
              have h : (Function.invFun (InitialRestriction f y) ⟨f x, k₂⟩).1 ≤ y ∧ (Function.invFun (InitialRestriction f x) ⟨f x, IsInSubProd (P := P) (S:= S) (f := f) x⟩).1 ≤ y ∧ f ((Function.invFun (InitialRestriction f y) ⟨f x, k₂⟩).1) = f ((Function.invFun (InitialRestriction f x) ⟨f x, IsInSubProd (P := P) (S:= S) (f := f) x⟩).1) := by
                constructor
                apply (Function.invFun (InitialRestriction f y) ⟨f x, k₂⟩).2
                constructor
                apply le_trans
                apply (Function.invFun (InitialRestriction f x) ⟨f x, IsInSubProd x⟩).2
                apply xley
                calc
                  f ((Function.invFun (InitialRestriction f y) ⟨f x, k₂⟩)).1  = ((InitialRestriction f y) ((Function.invFun (InitialRestriction f y) ⟨f x, k₂⟩))).1 := by rfl
                  _ = f x := by rw[(IsInverse (f:= InitialRestriction f y) (h:= (hf y).1)).right]
                  _ = ((InitialRestriction f x) ((Function.invFun (InitialRestriction f x) ⟨f x, IsInSubProd (P := P) (S:= S) (f := f) x⟩))).1 := by
                    rw[(IsInverse (f:= InitialRestriction f x) (h:= (hf x).1)).right]
                  _ = f ((Function.invFun (InitialRestriction f x) ⟨f x, IsInSubProd (P := P) (S:= S) (f := f) x⟩)).1 := by rfl
              apply Exists.intro y h
        exact k'
      exact Quot.sound k
    have h' : (IsNormalHom' x) * (IsNormalHom' y) = IsNormalHom' x := by
      calc
        (IsNormalHom' x) * (IsNormalHom' y) = (Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r ⟨(f x, x), by apply IsInSubProd x⟩) * (Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r ⟨(f y, y), by apply IsInSubProd y⟩) := by apply Eq.refl
         _ = Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r (⟨(f x, x), by apply IsInSubProd x⟩ * ⟨(f y, y), by apply IsInSubProd y⟩) := by apply Eq.refl
         _ =  Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r (⟨(f x * f y, x * y), k₁⟩) := by rfl
         _ = Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r (⟨(f x , y), k₂⟩) := by
          have h' : f x * f y = f x := by
            have h'' : f x ≤ f y := by
              apply f.monotone'
              apply xley
            apply h''
          have k' : x * y = y := by rfl
          simp_all[h',k']
         _ =  Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r (⟨(f x , x), by apply IsInSubProd x⟩) := by apply h''
    apply h'

lemma IsEqual  {α β : Type u} {P : PartialOrder α} {S : SemilatticeInf β} {f : α →o β} {hf : ∀ a : α, IsIso (InitialRestriction f a)} : ∀ w, w = (Function.invFun (InitialRestriction f w) ⟨f w, IsInSubProd (α := α) (β:= β) (P:= P) (S := S) (f:= f)  w⟩).1 := by
    intro x
    have h' : ((InitialRestriction f x) ⟨x, le_refl x⟩).1 = ((InitialRestriction f x) (Function.invFun (InitialRestriction f x) ⟨f x, IsInSubProd (α := α) (β:= β) (P:= P) (S := S) (f:= f)  x⟩)).1 := by
      calc
          ((InitialRestriction f x) ⟨x, le_refl x⟩).1 = f x := by rfl
          _ = ((InitialRestriction f x) (Function.invFun (InitialRestriction f x) ⟨f x, IsInSubProd (α := α) (β:= β) (P:= P) (S := S) (f:= f)  x⟩)).1 := by rw[(IsInverse (f:= InitialRestriction f x) (h:= (hf x).1)).right]
    have h'' : ((InitialRestriction f x) ⟨x, le_refl x⟩) = ((InitialRestriction f x) (Function.invFun (InitialRestriction f x) ⟨f x, IsInSubProd (α := α) (β:= β) (P:= P) (S := S) (f:= f)  x⟩)) := by
        exact SetCoe.ext h'
    have h''' : MapTo x x = (Function.invFun (InitialRestriction f x) ⟨f x, IsInSubProd (α := α) (β:= β) (P:= P) (S := S) (f:= f)  x⟩) := by
      apply (hf x).1.1
      calc
          (InitialRestriction f x) (MapTo x x) = (InitialRestriction f x) ⟨x, le_refl x⟩ := by rfl
          _ = (InitialRestriction f x) (Function.invFun (InitialRestriction f x) ⟨f x, IsInSubProd (α := α) (β:= β) (P:= P) (S := S) (f:= f)  x⟩) := by apply h''
    calc
        x = (MapTo x x).1 := by rfl
        _ = (Function.invFun (InitialRestriction f x) ⟨f x, IsInSubProd (α := α) (β:= β) (P:= P) (S := S) (f:= f)  x⟩).1 := by
          rw[h''']

--Muestro que el homomorfismo anterior es biyectivo
lemma NormalHomIsBij {α β : Type u} {P : PartialOrder α} {S : SemilatticeInf β} {f : α →o β} {hf : ∀ a : α, IsIso (InitialRestriction f a)} : bijective (IsNormalHom' (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf) ):= by

  constructor

  -------------------------------------------Inyectividad--------------------------------------------------
  intro x y fxy
  have h' : (Function.invFun (InitialRestriction f x) ⟨f x, IsInSubProd (α := α) (β:= β) (P:= P) (S := S) (f:= f) x⟩).1 = (Function.invFun (InitialRestriction f y) ⟨f y, IsInSubProd (α := α) (β:= β) (P:= P) (S := S) (f:= f) y⟩).1 := by
    calc
      (Function.invFun (InitialRestriction f x) ⟨f x, IsInSubProd (α := α) (β:= β) (P:= P) (S := S) (f:= f)  x⟩).1 = Proy ⟨(f x,x),IsInSubProd x⟩  := by rfl
      _ = Proy ⟨(f y,y),IsInSubProd y⟩ := by
        have h'' :  Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r ⟨(f x, x), by apply IsInSubProd x⟩ =  Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r ⟨(f y, y), by apply IsInSubProd (α := α) (β:= β) (P:= P) (S := S) (f:= f)  y⟩ :=
          by exact fxy
        apply CongSound (α := SubProducto f) (h:= NormalQuot)
        apply h''


  calc
    x = (Function.invFun (InitialRestriction f x) ⟨f x, IsInSubProd (α := α) (β:= β) (P:= P) (S := S) (f:= f)  x⟩).1 := by
     apply IsEqual (α := α) (β := β) (P := P) (S := S) (f := f) (hf := hf) x
    _ = (Function.invFun (InitialRestriction f y) ⟨f y, IsInSubProd (α := α) (β:= β) (P:= P) (S := S) (f:= f)  y⟩).1 := by apply h'
    _ = y := by rw[← (IsEqual (α := α) (β := β) (P := P) (S := S) (f := f) (hf := hf) y)]

  ---------------------------------------------- Suryectividad --------------------------------------------------------
  intro x
  have h' : ∃ x', x = Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r x' := by exact QuotForm x
  rcases h' with ⟨x', hx⟩
  let x'' := Proy x'
  have h'' : IsNormalHom x'' = x := by
    calc
      IsNormalHom x'' = Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r ⟨(f x'' ,x''), IsInSubProd x''⟩ := by rfl
      _ = Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r x' := by
        have k : Proy ⟨(f x'' ,x''), IsInSubProd (α := α) (β:= β) (P:= P) (S := S) (f:= f) x''⟩ = Proy x' := by
          calc
            Proy ⟨(f x'' ,x''), IsInSubProd (α := α) (β:= β) (P:= P) (S := S) (f:= f) x''⟩ = (Function.invFun (InitialRestriction f x'') ⟨f x'' ,IsInSubProd (α := α) (β:= β) (P:= P) (S := S) (f:= f) (x'')⟩).1 := by rfl
            _ = x'' := by
              apply Eq.symm
              apply IsEqual (α := α) (β := β) (P := P) (S := S) (f := f) (hf := hf) x''
            _ = ((Function.invFun) (InitialRestriction f x'.1.2) ⟨x'.1.1, x'.2⟩).1 := by
              rfl
        exact Quot.sound k
      _ = x := by simp_all[hx]
  exact Exists.intro x'' h''



noncomputable def NormalIso {α β : Type u} [Nonempty α] {P : PartialOrder α} {S : SemilatticeInf β} {f : α →o β} {hf : ∀ a : α, IsIso (InitialRestriction f a)} : α ≃o Quot (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r where
  toFun := (IsNormalHom' (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf) )
  invFun := Function.invFun (IsNormalHom (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf) )
  left_inv := by exact Function.leftInverse_invFun fun ⦃x y⦄ => And.left NormalHomIsBij x y
  right_inv := by exact Function.rightInverse_invFun fun ⦃x⦄ => And.right NormalHomIsBij x
  map_rel_iff' := by
    intro x y
    constructor
    simp_all
    intro xley
    have k : Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r ⟨(f x, x), by apply IsInSubProd x⟩ = Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r ⟨((f x ⊓ f y), y), _⟩ := by
     calc
      Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r ⟨(f x, x), by apply IsInSubProd x⟩ = IsNormalHom' x := by apply Eq.refl
      _ = (IsNormalHom' x) * (IsNormalHom' y) := by
        have h' : RightNormalBand.leq (IsNormalHom' x) (IsNormalHom' y) := by apply xley
        rw[h']
      _ = Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r ⟨(f x, x), by apply IsInSubProd x⟩ * Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r ⟨(f y, y), by apply IsInSubProd y⟩ := by apply Eq.refl
      _ = Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r ⟨(f x, x) * (f y, y), _⟩ := by apply Eq.refl
      _ = Quot.mk (NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf)).r ⟨((f x ⊓ f y), y), _⟩ := by apply Eq.refl
    have h' : Proy ⟨(f x, x), by apply IsInSubProd x⟩ = Proy ⟨((f x ⊓ f y), y), _⟩ := by
      have h'' : KerProy ⟨(f x, x), by apply IsInSubProd x⟩ ⟨((f x ⊓ f y), y), _⟩ := by
        apply CongSound (h := NormalQuot (α := α) (β:= β) (P:= P) (S := S) (f:= f) (hf := hf))
        apply k
      exact h''
    calc
      x = (Function.invFun (InitialRestriction f x) ⟨f x, by apply IsInSubProd x⟩).1 := by
        exact IsEqual (α := α) (β := β) (P := P) (S := S) (f := f) (hf := hf) x
     _ = Proy ⟨(f x, x), by apply IsInSubProd x⟩ := by apply Eq.refl
     _ = Proy ⟨((f x ⊓ f y), y), _⟩ := by apply h'
     _ = Function.invFun (InitialRestriction f y) ⟨f x ⊓ f y, _⟩ := by apply Eq.refl
     _ ≤ y := by apply (Function.invFun (InitialRestriction f y) ⟨f x ⊓ f y, _⟩).2
    apply IsNormalHom.monotone'


def IsNormal' {α : Type u} (_ : PartialOrder α) : Prop := --Caracterización orden teorética de los posets normales
∃ (α' : Type u), ∃(_ : SemilatticeInf α'), ∃(f : OrderHom α α'), ∀(a : α), IsIso (InitialRestriction f a)


theorem NormalPosetsCharacterization {α : Type u} [P : PartialOrder α] [Nonempty α] : IsNormal P ↔ IsNormal' P := by
  constructor
  intro x
  rcases x with ⟨U,hu⟩
  rcases hu with ⟨A,HA⟩
  rcases HA with ⟨g,_⟩
  have g' : IsIso (IsotoOrderHom g) := by apply IsoisIso
  have w : ∀ a : α, IsIso (InitialRestriction (OrderHom.comp (OrderProj (α:= U) (h := ProjectCong A)) g) a) := by
    apply IsoComp'
    apply RestrictProjectIsIso
    apply g'
  have hf : ∃ f : OrderHom α (Quot (ProjectCong A).r), ∀(a : α), IsIso (InitialRestriction f a) := by exact Exists.intro (OrderHom.comp OrderProj ↑g) w
  have hf' : ∃ _ : SemilatticeInf (Quot (ProjectCong A).r),∃ f : OrderHom α (Quot (ProjectCong A).r),  ∀(a : α), IsIso (InitialRestriction f a) := by refine Exists.intro (QuotSemilattice A) hf
  simp_all
  apply Exists.intro (Quot (ProjectCong A).r)
  use (QuotSemilattice A)
  intro x
  rcases x with ⟨S, hs⟩
  rcases hs with ⟨f', hf⟩
  rcases hf with ⟨g, hg⟩
  use Quot (NormalQuot (P := P) (S := f') (f := g) (hf := hg)).r
  use QuotBand (h := NormalQuot (P := P) (S := f') (f := g) (hf := hg))
  use NormalIso
