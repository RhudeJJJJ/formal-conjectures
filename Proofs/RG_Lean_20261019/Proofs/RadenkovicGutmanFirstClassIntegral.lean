/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanCellPartition
import Proofs.RadenkovicGutmanFirstClassCells00
import Proofs.RadenkovicGutmanFirstClassCells01
import Proofs.RadenkovicGutmanFirstClassCells02
import Proofs.RadenkovicGutmanFirstClassCells03
import Proofs.RadenkovicGutmanFirstClassCells04
import Proofs.RadenkovicGutmanFirstClassCells05
import Proofs.RadenkovicGutmanFirstClassCells06
import Proofs.RadenkovicGutmanFirstClassCells07

/-! The complete finite interval payment for degree one and physical arms
one/one. Positive escape payments and the other arm classes remain separate. -/
namespace Gebendorfer.RadenkovicGutman.FirstClassIntegral
open CellPartition FirstClassCells
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slice00 : Slice := ⟨cell00,(1/1000),(1/500)⟩
theorem slice00_checked : CellPartition.accepts 1 0 0 slice00=true :=
  accepts_of_checks 1 0 0 slice00 cell00_checked (by decide +kernel)
def slice01 : Slice := ⟨cell01,(1/500),(7/2000)⟩
theorem slice01_checked : CellPartition.accepts 1 0 0 slice01=true :=
  accepts_of_checks 1 0 0 slice01 cell01_checked (by decide +kernel)
def slice02 : Slice := ⟨cell02,(7/2000),(1/200)⟩
theorem slice02_checked : CellPartition.accepts 1 0 0 slice02=true :=
  accepts_of_checks 1 0 0 slice02 cell02_checked (by decide +kernel)
def slice03 : Slice := ⟨cell03,(1/200),(3/400)⟩
theorem slice03_checked : CellPartition.accepts 1 0 0 slice03=true :=
  accepts_of_checks 1 0 0 slice03 cell03_checked (by decide +kernel)
def slice04 : Slice := ⟨cell04,(3/400),(1/100)⟩
theorem slice04_checked : CellPartition.accepts 1 0 0 slice04=true :=
  accepts_of_checks 1 0 0 slice04 cell04_checked (by decide +kernel)
def slice05 : Slice := ⟨cell05,(1/100),(3/200)⟩
theorem slice05_checked : CellPartition.accepts 1 0 0 slice05=true :=
  accepts_of_checks 1 0 0 slice05 cell05_checked (by decide +kernel)
def slice06 : Slice := ⟨cell06,(3/200),(1/50)⟩
theorem slice06_checked : CellPartition.accepts 1 0 0 slice06=true :=
  accepts_of_checks 1 0 0 slice06 cell06_checked (by decide +kernel)
def slice07 : Slice := ⟨cell07,(1/50),(11/400)⟩
theorem slice07_checked : CellPartition.accepts 1 0 0 slice07=true :=
  accepts_of_checks 1 0 0 slice07 cell07_checked (by decide +kernel)
def slice08 : Slice := ⟨cell08,(11/400),(7/200)⟩
theorem slice08_checked : CellPartition.accepts 1 0 0 slice08=true :=
  accepts_of_checks 1 0 0 slice08 cell08_checked (by decide +kernel)
def slice09 : Slice := ⟨cell09,(7/200),(17/400)⟩
theorem slice09_checked : CellPartition.accepts 1 0 0 slice09=true :=
  accepts_of_checks 1 0 0 slice09 cell09_checked (by decide +kernel)
def slice10 : Slice := ⟨cell10,(17/400),(1/20)⟩
theorem slice10_checked : CellPartition.accepts 1 0 0 slice10=true :=
  accepts_of_checks 1 0 0 slice10 cell10_checked (by decide +kernel)
def slice11 : Slice := ⟨cell11,(1/20),(1/16)⟩
theorem slice11_checked : CellPartition.accepts 1 0 0 slice11=true :=
  accepts_of_checks 1 0 0 slice11 cell11_checked (by decide +kernel)
def slice12 : Slice := ⟨cell12,(1/16),(3/40)⟩
theorem slice12_checked : CellPartition.accepts 1 0 0 slice12=true :=
  accepts_of_checks 1 0 0 slice12 cell12_checked (by decide +kernel)
def slice13 : Slice := ⟨cell13,(3/40),(7/80)⟩
theorem slice13_checked : CellPartition.accepts 1 0 0 slice13=true :=
  accepts_of_checks 1 0 0 slice13 cell13_checked (by decide +kernel)
def slice14 : Slice := ⟨cell14,(7/80),(1/10)⟩
theorem slice14_checked : CellPartition.accepts 1 0 0 slice14=true :=
  accepts_of_checks 1 0 0 slice14 cell14_checked (by decide +kernel)
def slice15 : Slice := ⟨cell15,(1/10),(9/80)⟩
theorem slice15_checked : CellPartition.accepts 1 0 0 slice15=true :=
  accepts_of_checks 1 0 0 slice15 cell15_checked (by decide +kernel)
def slice16 : Slice := ⟨cell16,(9/80),(1/8)⟩
theorem slice16_checked : CellPartition.accepts 1 0 0 slice16=true :=
  accepts_of_checks 1 0 0 slice16 cell16_checked (by decide +kernel)
def slice17 : Slice := ⟨cell17,(1/8),(11/80)⟩
theorem slice17_checked : CellPartition.accepts 1 0 0 slice17=true :=
  accepts_of_checks 1 0 0 slice17 cell17_checked (by decide +kernel)
def slice18 : Slice := ⟨cell18,(11/80),(3/20)⟩
theorem slice18_checked : CellPartition.accepts 1 0 0 slice18=true :=
  accepts_of_checks 1 0 0 slice18 cell18_checked (by decide +kernel)
def slice19 : Slice := ⟨cell19,(3/20),(13/80)⟩
theorem slice19_checked : CellPartition.accepts 1 0 0 slice19=true :=
  accepts_of_checks 1 0 0 slice19 cell19_checked (by decide +kernel)
def slice20 : Slice := ⟨cell20,(13/80),(7/40)⟩
theorem slice20_checked : CellPartition.accepts 1 0 0 slice20=true :=
  accepts_of_checks 1 0 0 slice20 cell20_checked (by decide +kernel)
def slice21 : Slice := ⟨cell21,(7/40),(1/5)⟩
theorem slice21_checked : CellPartition.accepts 1 0 0 slice21=true :=
  accepts_of_checks 1 0 0 slice21 cell21_checked (by decide +kernel)
def slice22 : Slice := ⟨cell22,(1/5),(7/32)⟩
theorem slice22_checked : CellPartition.accepts 1 0 0 slice22=true :=
  accepts_of_checks 1 0 0 slice22 cell22_checked (by decide +kernel)
def slice23 : Slice := ⟨cell23,(7/32),(19/80)⟩
theorem slice23_checked : CellPartition.accepts 1 0 0 slice23=true :=
  accepts_of_checks 1 0 0 slice23 cell23_checked (by decide +kernel)
def slice24 : Slice := ⟨cell24,(19/80),(41/160)⟩
theorem slice24_checked : CellPartition.accepts 1 0 0 slice24=true :=
  accepts_of_checks 1 0 0 slice24 cell24_checked (by decide +kernel)
def slice25 : Slice := ⟨cell25,(41/160),(11/40)⟩
theorem slice25_checked : CellPartition.accepts 1 0 0 slice25=true :=
  accepts_of_checks 1 0 0 slice25 cell25_checked (by decide +kernel)
def slice26 : Slice := ⟨cell26,(11/40),(47/160)⟩
theorem slice26_checked : CellPartition.accepts 1 0 0 slice26=true :=
  accepts_of_checks 1 0 0 slice26 cell26_checked (by decide +kernel)
def slice27 : Slice := ⟨cell27,(47/160),(5/16)⟩
theorem slice27_checked : CellPartition.accepts 1 0 0 slice27=true :=
  accepts_of_checks 1 0 0 slice27 cell27_checked (by decide +kernel)
def slice28 : Slice := ⟨cell28,(5/16),(7/20)⟩
theorem slice28_checked : CellPartition.accepts 1 0 0 slice28=true :=
  accepts_of_checks 1 0 0 slice28 cell28_checked (by decide +kernel)
def slice29 : Slice := ⟨cell29,(7/20),(31/80)⟩
theorem slice29_checked : CellPartition.accepts 1 0 0 slice29=true :=
  accepts_of_checks 1 0 0 slice29 cell29_checked (by decide +kernel)
def slice30 : Slice := ⟨cell30,(31/80),(17/40)⟩
theorem slice30_checked : CellPartition.accepts 1 0 0 slice30=true :=
  accepts_of_checks 1 0 0 slice30 cell30_checked (by decide +kernel)
def slice31 : Slice := ⟨cell31,(17/40),(37/80)⟩
theorem slice31_checked : CellPartition.accepts 1 0 0 slice31=true :=
  accepts_of_checks 1 0 0 slice31 cell31_checked (by decide +kernel)
def slice32 : Slice := ⟨cell32,(37/80),(1/2)⟩
theorem slice32_checked : CellPartition.accepts 1 0 0 slice32=true :=
  accepts_of_checks 1 0 0 slice32 cell32_checked (by decide +kernel)
def slice33 : Slice := ⟨cell33,(1/2),(9/16)⟩
theorem slice33_checked : CellPartition.accepts 1 0 0 slice33=true :=
  accepts_of_checks 1 0 0 slice33 cell33_checked (by decide +kernel)
def slice34 : Slice := ⟨cell34,(9/16),(5/8)⟩
theorem slice34_checked : CellPartition.accepts 1 0 0 slice34=true :=
  accepts_of_checks 1 0 0 slice34 cell34_checked (by decide +kernel)
def slice35 : Slice := ⟨cell35,(5/8),(11/16)⟩
theorem slice35_checked : CellPartition.accepts 1 0 0 slice35=true :=
  accepts_of_checks 1 0 0 slice35 cell35_checked (by decide +kernel)
def slice36 : Slice := ⟨cell36,(11/16),(3/4)⟩
theorem slice36_checked : CellPartition.accepts 1 0 0 slice36=true :=
  accepts_of_checks 1 0 0 slice36 cell36_checked (by decide +kernel)
def slice37 : Slice := ⟨cell37,(3/4),(13/16)⟩
theorem slice37_checked : CellPartition.accepts 1 0 0 slice37=true :=
  accepts_of_checks 1 0 0 slice37 cell37_checked (by decide +kernel)
def slice38 : Slice := ⟨cell38,(13/16),(7/8)⟩
theorem slice38_checked : CellPartition.accepts 1 0 0 slice38=true :=
  accepts_of_checks 1 0 0 slice38 cell38_checked (by decide +kernel)
def slice39 : Slice := ⟨cell39,(7/8),1⟩
theorem slice39_checked : CellPartition.accepts 1 0 0 slice39=true :=
  accepts_of_checks 1 0 0 slice39 cell39_checked (by decide +kernel)
def slice40 : Slice := ⟨cell40,1,(8/7)⟩
theorem slice40_checked : CellPartition.accepts 1 0 0 slice40=true :=
  accepts_of_checks 1 0 0 slice40 cell40_checked (by decide +kernel)
def slice41 : Slice := ⟨cell41,(8/7),(4/3)⟩
theorem slice41_checked : CellPartition.accepts 1 0 0 slice41=true :=
  accepts_of_checks 1 0 0 slice41 cell41_checked (by decide +kernel)
def slice42 : Slice := ⟨cell42,(4/3),(16/11)⟩
theorem slice42_checked : CellPartition.accepts 1 0 0 slice42=true :=
  accepts_of_checks 1 0 0 slice42 cell42_checked (by decide +kernel)
def slice43 : Slice := ⟨cell43,(16/11),(8/5)⟩
theorem slice43_checked : CellPartition.accepts 1 0 0 slice43=true :=
  accepts_of_checks 1 0 0 slice43 cell43_checked (by decide +kernel)
def slice44 : Slice := ⟨cell44,(8/5),(16/9)⟩
theorem slice44_checked : CellPartition.accepts 1 0 0 slice44=true :=
  accepts_of_checks 1 0 0 slice44 cell44_checked (by decide +kernel)
def slice45 : Slice := ⟨cell45,(16/9),2⟩
theorem slice45_checked : CellPartition.accepts 1 0 0 slice45=true :=
  accepts_of_checks 1 0 0 slice45 cell45_checked (by decide +kernel)
def slice46 : Slice := ⟨cell46,2,(32/15)⟩
theorem slice46_checked : CellPartition.accepts 1 0 0 slice46=true :=
  accepts_of_checks 1 0 0 slice46 cell46_checked (by decide +kernel)
def slice47 : Slice := ⟨cell47,(32/15),(16/7)⟩
theorem slice47_checked : CellPartition.accepts 1 0 0 slice47=true :=
  accepts_of_checks 1 0 0 slice47 cell47_checked (by decide +kernel)
def slice48 : Slice := ⟨cell48,(16/7),(32/13)⟩
theorem slice48_checked : CellPartition.accepts 1 0 0 slice48=true :=
  accepts_of_checks 1 0 0 slice48 cell48_checked (by decide +kernel)
def slice49 : Slice := ⟨cell49,(32/13),(8/3)⟩
theorem slice49_checked : CellPartition.accepts 1 0 0 slice49=true :=
  accepts_of_checks 1 0 0 slice49 cell49_checked (by decide +kernel)
def slice50 : Slice := ⟨cell50,(8/3),(32/11)⟩
theorem slice50_checked : CellPartition.accepts 1 0 0 slice50=true :=
  accepts_of_checks 1 0 0 slice50 cell50_checked (by decide +kernel)
def slice51 : Slice := ⟨cell51,(32/11),(16/5)⟩
theorem slice51_checked : CellPartition.accepts 1 0 0 slice51=true :=
  accepts_of_checks 1 0 0 slice51 cell51_checked (by decide +kernel)
def slice52 : Slice := ⟨cell52,(16/5),(64/19)⟩
theorem slice52_checked : CellPartition.accepts 1 0 0 slice52=true :=
  accepts_of_checks 1 0 0 slice52 cell52_checked (by decide +kernel)
def slice53 : Slice := ⟨cell53,(64/19),(32/9)⟩
theorem slice53_checked : CellPartition.accepts 1 0 0 slice53=true :=
  accepts_of_checks 1 0 0 slice53 cell53_checked (by decide +kernel)
def slice54 : Slice := ⟨cell54,(32/9),(64/17)⟩
theorem slice54_checked : CellPartition.accepts 1 0 0 slice54=true :=
  accepts_of_checks 1 0 0 slice54 cell54_checked (by decide +kernel)
def slice55 : Slice := ⟨cell55,(64/17),4⟩
theorem slice55_checked : CellPartition.accepts 1 0 0 slice55=true :=
  accepts_of_checks 1 0 0 slice55 cell55_checked (by decide +kernel)
def slice56 : Slice := ⟨cell56,4,(64/15)⟩
theorem slice56_checked : CellPartition.accepts 1 0 0 slice56=true :=
  accepts_of_checks 1 0 0 slice56 cell56_checked (by decide +kernel)
def slice57 : Slice := ⟨cell57,(64/15),(32/7)⟩
theorem slice57_checked : CellPartition.accepts 1 0 0 slice57=true :=
  accepts_of_checks 1 0 0 slice57 cell57_checked (by decide +kernel)
def slice58 : Slice := ⟨cell58,(32/7),(64/13)⟩
theorem slice58_checked : CellPartition.accepts 1 0 0 slice58=true :=
  accepts_of_checks 1 0 0 slice58 cell58_checked (by decide +kernel)
def slice59 : Slice := ⟨cell59,(64/13),(16/3)⟩
theorem slice59_checked : CellPartition.accepts 1 0 0 slice59=true :=
  accepts_of_checks 1 0 0 slice59 cell59_checked (by decide +kernel)
def slice60 : Slice := ⟨cell60,(16/3),(64/11)⟩
theorem slice60_checked : CellPartition.accepts 1 0 0 slice60=true :=
  accepts_of_checks 1 0 0 slice60 cell60_checked (by decide +kernel)
def slice61 : Slice := ⟨cell61,(64/11),(32/5)⟩
theorem slice61_checked : CellPartition.accepts 1 0 0 slice61=true :=
  accepts_of_checks 1 0 0 slice61 cell61_checked (by decide +kernel)
def slice62 : Slice := ⟨cell62,(32/5),(64/9)⟩
theorem slice62_checked : CellPartition.accepts 1 0 0 slice62=true :=
  accepts_of_checks 1 0 0 slice62 cell62_checked (by decide +kernel)
def slice63 : Slice := ⟨cell63,(64/9),8⟩
theorem slice63_checked : CellPartition.accepts 1 0 0 slice63=true :=
  accepts_of_checks 1 0 0 slice63 cell63_checked (by decide +kernel)
def partition : List Slice := [slice00,slice01,slice02,slice03,slice04,slice05,slice06,slice07,slice08,slice09,slice10,slice11,slice12,slice13,slice14,slice15,slice16,slice17,slice18,slice19,slice20,slice21,slice22,slice23,slice24,slice25,slice26,slice27,slice28,slice29,slice30,slice31,slice32,slice33,slice34,slice35,slice36,slice37,slice38,slice39,slice40,slice41,slice42,slice43,slice44,slice45,slice46,slice47,slice48,slice49,slice50,slice51,slice52,slice53,slice54,slice55,slice56,slice57,slice58,slice59,slice60,slice61,slice62,slice63]
theorem partition_checked : checkAt 1 0 0 (1/1000) 8 partition=true := by
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
  apply checked_cons _ _ _ _ _ _ _ rfl slice25_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice26_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice27_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice28_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice29_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice30_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice31_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice32_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice33_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice34_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice35_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice36_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice37_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice38_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice39_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice40_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice41_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice42_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice43_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice44_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice45_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice46_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice47_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice48_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice49_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice50_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice51_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice52_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice53_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice54_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice55_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice56_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice57_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice58_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice59_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice60_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice61_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice62_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice63_checked
  decide +kernel
theorem payment_checked : (decide (payment partition=(3354807096003580173625700869/134722032206546673478926336000)))=true := by decide +kernel
noncomputable section
open CoreQuotient
open scoped Classical
theorem actual_finite_payment {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (hd : C.degree u=1) :
    (((3354807096003580173625700869/134722032206546673478926336000) : ℚ) : ℝ) ≤ ∫ y : ℝ in ((1/1000 : ℚ) : ℝ)..((8 : ℚ) : ℝ),
      MixedGraphIntegral.logarithm (source C u 0 0) (fused C u 0 0) 2 y := by
  have hc : checkAt ((1 : ℕ) : ℚ) 0 0 (1/1000) 8 partition=true := by
    simpa only [Nat.cast_one] using partition_checked
  have h := CellPartition.integral_lower C u 0 0 1 (by decide) hd 0 0
    (by decide +kernel) (by decide +kernel) (1/1000) 8 (by norm_num) partition hc
  rw [show payment partition=(3354807096003580173625700869/134722032206546673478926336000) from of_decide_eq_true payment_checked] at h
  exact h
#print axioms partition_checked
#print axioms payment_checked
#print axioms actual_finite_payment
end
end Gebendorfer.RadenkovicGutman.FirstClassIntegral
