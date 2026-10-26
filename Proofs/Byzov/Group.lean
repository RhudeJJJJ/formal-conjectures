module

public import Proofs.Byzov.NormalForm

/-! # The exact conjectured direct and semidirect product

The cyclic action is the original imported positive shift. Parameter a acts on
vertices by translation -a, so composition agrees with that action exactly.
Odd m splits the binary function group into constants and augmentation.
-/

@[expose] public section
namespace ByzovPushkarev.Certificate
open Finset

abbrev Target (n : ℕ) := Multiplicative (ZMod 2) ×
  SemidirectProduct (Multiplicative (augmentation (orderParameter n)))
    (Multiplicative (Coord n)) (cyclicAction (orderParameter n))

def decode (n : ℕ) (p : Target n) (t : C n) : ZMod 2 :=
  p.1.toAdd+p.2.left.toAdd.val t

def coordinate (n : ℕ) (p : Target n) : C n := p.2.right.toAdd

theorem decode_mul (n : ℕ) (p q : Target n) (t : C n) :
    decode n (p*q) t = decode n p t+decode n q (t+coordinate n p) := by
  change (p.1.toAdd+q.1.toAdd)+
      (p.2.left.toAdd.val t+q.2.left.toAdd.val (t+p.2.right.toAdd)) =
    (p.1.toAdd+p.2.left.toAdd.val t)+(q.1.toAdd+q.2.left.toAdd.val (t+p.2.right.toAdd))
  ring

@[simp] theorem coordinate_mul (n : ℕ) (p q : Target n) :
    coordinate n (p*q) = coordinate n p+coordinate n q := rfl

@[simp] theorem decode_one (n : ℕ) (t : C n) : decode n 1 t = 0 := by
  change (0 : ZMod 2)+0 = 0
  exact zero_add _

@[simp] theorem coordinate_one (n : ℕ) : coordinate n 1 = 0 := rfl

def targetHom (n : ℕ) (hn : 2 ≤ n) : Target n →* Aut n where
  toFun p := parameterAut n hn (decode n p) (coordinate n p)
  map_one' := by
    apply RelIso.ext
    intro u
    change swap (decode n 1) (translate (-(coordinate n 1)) u) = u
    have hf : decode n 1 = (fun _ => 0) := funext (decode_one n)
    rw [hf,coordinate_one,neg_zero,translate_zero,swap_zero]
  map_mul' p q := by
    apply RelIso.ext
    intro u
    change swap (decode n (p*q)) (translate (-(coordinate n (p*q))) u) =
      swap (decode n p) (translate (-(coordinate n p))
        (swap (decode n q) (translate (-(coordinate n q)) u)))
    rw [coordinate_mul,neg_add,translate_swap,← swap_add,translate_translate]
    congr 1
    funext t
    simpa only [sub_neg_eq_add] using decode_mul n p q t

theorem sum_constant (n : ℕ) (c : ZMod 2) : (∑ _t : C n, c) = c := by
  rw [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
  have hm : ((M n : ℕ) : ZMod 2) = 1 := by norm_num [M,Nat.cast_add,Nat.cast_mul]
  rw [hm,one_mul]

theorem decode_sum (n : ℕ) (p : Target n) : (∑ t : C n, decode n p t) = p.1.toAdd := by
  change (∑ t : C n, (p.1.toAdd+p.2.left.toAdd.val t)) = p.1.toAdd
  rw [Finset.sum_add_distrib,sum_constant]
  have hw : (∑ t : C n, p.2.left.toAdd.val t) = 0 := p.2.left.toAdd.property
  rw [hw,add_zero]

theorem target_ext (n : ℕ) (p q : Target n)
    (ha : coordinate n p = coordinate n q) (hf : decode n p = decode n q) : p = q := by
  have hc : p.1.toAdd = q.1.toAdd := by
    have hh := congrArg (fun f : C n → ZMod 2 => ∑ t, f t) hf
    simpa only [decode_sum] using hh
  apply Prod.ext
  · change p.1.toAdd = q.1.toAdd
    exact hc
  · apply SemidirectProduct.ext
    · change p.2.left.toAdd = q.2.left.toAdd
      apply Subtype.ext
      funext t
      have hh := congrFun hf t
      change p.1.toAdd+p.2.left.toAdd.val t = q.1.toAdd+q.2.left.toAdd.val t at hh
      rw [hc] at hh
      exact add_left_cancel hh
    · change coordinate n p = coordinate n q
      exact ha

theorem targetHom_injective (n : ℕ) (hn : 2 ≤ n) : Function.Injective (targetHom n hn) := by
  intro p q h
  have hh := parameterAut_injective n hn (decode n p) (decode n q)
    (coordinate n p) (coordinate n q) h
  exact target_ext n p q hh.2 hh.1

theorem targetHom_surjective (n : ℕ) (hn : 2 ≤ n) : Function.Surjective (targetHom n hn) := by
  intro e
  obtain ⟨f,a,he⟩ := parameterAut_surjective n hn e
  let c : ZMod 2 := ∑ t : C n, f t
  let w : augmentation (orderParameter n) := ⟨fun t => f t-c,by
    change (∑ t : C n, (f t-c)) = 0
    rw [Finset.sum_sub_distrib,sum_constant]
    exact sub_self c⟩
  let p : Target n := (Multiplicative.ofAdd c,
    ⟨Multiplicative.ofAdd w,Multiplicative.ofAdd a⟩)
  refine ⟨p,?_⟩
  change parameterAut n hn (decode n p) (coordinate n p) = e
  have hf : decode n p = f := by
    funext t
    change c+(f t-c) = f t
    ring
  have ha : coordinate n p = a := rfl
  rw [hf,ha]
  exact he

end ByzovPushkarev.Certificate
