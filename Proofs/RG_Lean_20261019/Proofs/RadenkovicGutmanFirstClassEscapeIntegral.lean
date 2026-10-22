/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanCellPartition
import Proofs.RadenkovicGutmanFirstClassEscapeCells00
import Proofs.RadenkovicGutmanFirstClassEscapeCells01
import Proofs.RadenkovicGutmanFirstClassEscapeCells02
import Proofs.RadenkovicGutmanFirstClassEscapeCells03

/-! The complete finite interval payment for degree one and physical arms
one/one. Positive escape payments and the other arm classes remain separate. -/
namespace Gebendorfer.RadenkovicGutman.FirstClassEscapeIntegral
open CellPartition FirstClassEscapeCells
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slice00 : Slice := ⟨cell00,8,(128/15)⟩
theorem slice00_checked : CellPartition.accepts 1 0 0 slice00=true :=
  accepts_of_checks 1 0 0 slice00 cell00_checked (by decide +kernel)
def slice01 : Slice := ⟨cell01,(128/15),(64/7)⟩
theorem slice01_checked : CellPartition.accepts 1 0 0 slice01=true :=
  accepts_of_checks 1 0 0 slice01 cell01_checked (by decide +kernel)
def slice02 : Slice := ⟨cell02,(64/7),(128/13)⟩
theorem slice02_checked : CellPartition.accepts 1 0 0 slice02=true :=
  accepts_of_checks 1 0 0 slice02 cell02_checked (by decide +kernel)
def slice03 : Slice := ⟨cell03,(128/13),(32/3)⟩
theorem slice03_checked : CellPartition.accepts 1 0 0 slice03=true :=
  accepts_of_checks 1 0 0 slice03 cell03_checked (by decide +kernel)
def slice04 : Slice := ⟨cell04,(32/3),(128/11)⟩
theorem slice04_checked : CellPartition.accepts 1 0 0 slice04=true :=
  accepts_of_checks 1 0 0 slice04 cell04_checked (by decide +kernel)
def slice05 : Slice := ⟨cell05,(128/11),(64/5)⟩
theorem slice05_checked : CellPartition.accepts 1 0 0 slice05=true :=
  accepts_of_checks 1 0 0 slice05 cell05_checked (by decide +kernel)
def slice06 : Slice := ⟨cell06,(64/5),(128/9)⟩
theorem slice06_checked : CellPartition.accepts 1 0 0 slice06=true :=
  accepts_of_checks 1 0 0 slice06 cell06_checked (by decide +kernel)
def slice07 : Slice := ⟨cell07,(128/9),16⟩
theorem slice07_checked : CellPartition.accepts 1 0 0 slice07=true :=
  accepts_of_checks 1 0 0 slice07 cell07_checked (by decide +kernel)
def slice08 : Slice := ⟨cell08,16,(128/7)⟩
theorem slice08_checked : CellPartition.accepts 1 0 0 slice08=true :=
  accepts_of_checks 1 0 0 slice08 cell08_checked (by decide +kernel)
def slice09 : Slice := ⟨cell09,(128/7),(64/3)⟩
theorem slice09_checked : CellPartition.accepts 1 0 0 slice09=true :=
  accepts_of_checks 1 0 0 slice09 cell09_checked (by decide +kernel)
def slice10 : Slice := ⟨cell10,(64/3),(256/11)⟩
theorem slice10_checked : CellPartition.accepts 1 0 0 slice10=true :=
  accepts_of_checks 1 0 0 slice10 cell10_checked (by decide +kernel)
def slice11 : Slice := ⟨cell11,(256/11),(128/5)⟩
theorem slice11_checked : CellPartition.accepts 1 0 0 slice11=true :=
  accepts_of_checks 1 0 0 slice11 cell11_checked (by decide +kernel)
def slice12 : Slice := ⟨cell12,(128/5),(256/9)⟩
theorem slice12_checked : CellPartition.accepts 1 0 0 slice12=true :=
  accepts_of_checks 1 0 0 slice12 cell12_checked (by decide +kernel)
def slice13 : Slice := ⟨cell13,(256/9),32⟩
theorem slice13_checked : CellPartition.accepts 1 0 0 slice13=true :=
  accepts_of_checks 1 0 0 slice13 cell13_checked (by decide +kernel)
def slice14 : Slice := ⟨cell14,32,(256/7)⟩
theorem slice14_checked : CellPartition.accepts 1 0 0 slice14=true :=
  accepts_of_checks 1 0 0 slice14 cell14_checked (by decide +kernel)
def slice15 : Slice := ⟨cell15,(256/7),(128/3)⟩
theorem slice15_checked : CellPartition.accepts 1 0 0 slice15=true :=
  accepts_of_checks 1 0 0 slice15 cell15_checked (by decide +kernel)
def slice16 : Slice := ⟨cell16,(128/3),(256/5)⟩
theorem slice16_checked : CellPartition.accepts 1 0 0 slice16=true :=
  accepts_of_checks 1 0 0 slice16 cell16_checked (by decide +kernel)
def slice17 : Slice := ⟨cell17,(256/5),64⟩
theorem slice17_checked : CellPartition.accepts 1 0 0 slice17=true :=
  accepts_of_checks 1 0 0 slice17 cell17_checked (by decide +kernel)
def slice18 : Slice := ⟨cell18,64,(256/3)⟩
theorem slice18_checked : CellPartition.accepts 1 0 0 slice18=true :=
  accepts_of_checks 1 0 0 slice18 cell18_checked (by decide +kernel)
def slice19 : Slice := ⟨cell19,(256/3),(512/5)⟩
theorem slice19_checked : CellPartition.accepts 1 0 0 slice19=true :=
  accepts_of_checks 1 0 0 slice19 cell19_checked (by decide +kernel)
def slice20 : Slice := ⟨cell20,(512/5),128⟩
theorem slice20_checked : CellPartition.accepts 1 0 0 slice20=true :=
  accepts_of_checks 1 0 0 slice20 cell20_checked (by decide +kernel)
def slice21 : Slice := ⟨cell21,128,(512/3)⟩
theorem slice21_checked : CellPartition.accepts 1 0 0 slice21=true :=
  accepts_of_checks 1 0 0 slice21 cell21_checked (by decide +kernel)
def slice22 : Slice := ⟨cell22,(512/3),256⟩
theorem slice22_checked : CellPartition.accepts 1 0 0 slice22=true :=
  accepts_of_checks 1 0 0 slice22 cell22_checked (by decide +kernel)
def slice23 : Slice := ⟨cell23,256,512⟩
theorem slice23_checked : CellPartition.accepts 1 0 0 slice23=true :=
  accepts_of_checks 1 0 0 slice23 cell23_checked (by decide +kernel)
def slice24 : Slice := ⟨cell24,512,1024⟩
theorem slice24_checked : CellPartition.accepts 1 0 0 slice24=true :=
  accepts_of_checks 1 0 0 slice24 cell24_checked (by decide +kernel)
def partition : List Slice := [slice00,slice01,slice02,slice03,slice04,slice05,slice06,slice07,slice08,slice09,slice10,slice11,slice12,slice13,slice14,slice15,slice16,slice17,slice18,slice19,slice20,slice21,slice22,slice23,slice24]
theorem partition_checked : checkAt 1 0 0 8 1024 partition=true := by
  unfold partition
  apply checked_cons _ _ _ _ _ _ _ rfl slice00_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice01_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice02_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice03_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice04_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice05_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice06_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice07_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice08_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice09_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice10_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice11_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice12_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice13_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice14_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice15_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice16_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice17_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice18_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice19_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice20_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice21_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice22_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice23_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice24_checked
  decide +kernel
theorem payment_checked : (decide (payment partition=(344921313615562164793601/3323734347200987010170880)))=true := by decide +kernel
noncomputable section
open CoreQuotient
open scoped Classical
theorem actual_finite_payment {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (hd : C.degree u=1) :
    (((344921313615562164793601/3323734347200987010170880) : ℚ) : ℝ) ≤ ∫ y : ℝ in ((8 : ℚ) : ℝ)..((1024 : ℚ) : ℝ),
      MixedGraphIntegral.logarithm (source C u 0 0) (fused C u 0 0) 2 y := by
  have hc : checkAt ((1 : ℕ) : ℚ) 0 0 8 1024 partition=true := by
    simpa only [Nat.cast_one] using partition_checked
  have h := CellPartition.integral_lower C u 0 0 1 (by decide) hd 0 0
    (by decide +kernel) (by decide +kernel) 8 1024 (by norm_num) partition hc
  rw [show payment partition=(344921313615562164793601/3323734347200987010170880) from of_decide_eq_true payment_checked] at h
  exact h
#print axioms partition_checked
#print axioms payment_checked
#print axioms actual_finite_payment
end
end Gebendorfer.RadenkovicGutman.FirstClassEscapeIntegral
