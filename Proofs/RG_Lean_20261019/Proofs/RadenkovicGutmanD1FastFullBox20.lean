/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFastPaidDegreeOneClass
import Proofs.RadenkovicGutmanD1FastFullBox20Cells00
import Proofs.RadenkovicGutmanD1FastFullBox20Cells01
import Proofs.RadenkovicGutmanD1FastFullBox20Cells02
import Proofs.RadenkovicGutmanD1FastFullBox20Cells03
import Proofs.RadenkovicGutmanD1FastFullBox20Cells04
import Proofs.RadenkovicGutmanD1FastFullBox20Cells05
import Proofs.RadenkovicGutmanD1FastFullBox20Cells06
import Proofs.RadenkovicGutmanD1FastFullBox20Cells07
import Proofs.RadenkovicGutmanD1FastFullBox20Cells08
import Proofs.RadenkovicGutmanD1FastFullBox20Cells09
namespace Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass20
open FastCellPartition
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slice000 : Slice := ⟨cell000,(1/1000),(1/500)⟩
theorem slice000_checked : FastCellPartition.accepts 1 1 4 slice000=true :=
  accepts_of_checks 1 1 4 slice000 cell000_checked (by decide +kernel)
def slice001 : Slice := ⟨cell001,(1/500),(1/200)⟩
theorem slice001_checked : FastCellPartition.accepts 1 1 4 slice001=true :=
  accepts_of_checks 1 1 4 slice001 cell001_checked (by decide +kernel)
def slice002 : Slice := ⟨cell002,(1/200),(1/100)⟩
theorem slice002_checked : FastCellPartition.accepts 1 1 4 slice002=true :=
  accepts_of_checks 1 1 4 slice002 cell002_checked (by decide +kernel)
def slice003 : Slice := ⟨cell003,(1/100),(1/50)⟩
theorem slice003_checked : FastCellPartition.accepts 1 1 4 slice003=true :=
  accepts_of_checks 1 1 4 slice003 cell003_checked (by decide +kernel)
def slice004 : Slice := ⟨cell004,(1/50),(1/20)⟩
theorem slice004_checked : FastCellPartition.accepts 1 1 4 slice004=true :=
  accepts_of_checks 1 1 4 slice004 cell004_checked (by decide +kernel)
def slice005 : Slice := ⟨cell005,(1/20),(1/10)⟩
theorem slice005_checked : FastCellPartition.accepts 1 1 4 slice005=true :=
  accepts_of_checks 1 1 4 slice005 cell005_checked (by decide +kernel)
def slice006 : Slice := ⟨cell006,(1/10),(1/5)⟩
theorem slice006_checked : FastCellPartition.accepts 1 1 4 slice006=true :=
  accepts_of_checks 1 1 4 slice006 cell006_checked (by decide +kernel)
def slice007 : Slice := ⟨cell007,(1/5),(1/2)⟩
theorem slice007_checked : FastCellPartition.accepts 1 1 4 slice007=true :=
  accepts_of_checks 1 1 4 slice007 cell007_checked (by decide +kernel)
def slice008 : Slice := ⟨cell008,(1/2),1⟩
theorem slice008_checked : FastCellPartition.accepts 1 1 4 slice008=true :=
  accepts_of_checks 1 1 4 slice008 cell008_checked (by decide +kernel)
def slice009 : Slice := ⟨cell009,1,2⟩
theorem slice009_checked : FastCellPartition.accepts 1 1 4 slice009=true :=
  accepts_of_checks 1 1 4 slice009 cell009_checked (by decide +kernel)
def slice010 : Slice := ⟨cell010,2,4⟩
theorem slice010_checked : FastCellPartition.accepts 1 1 4 slice010=true :=
  accepts_of_checks 1 1 4 slice010 cell010_checked (by decide +kernel)
def slice011 : Slice := ⟨cell011,4,8⟩
theorem slice011_checked : FastCellPartition.accepts 1 1 4 slice011=true :=
  accepts_of_checks 1 1 4 slice011 cell011_checked (by decide +kernel)
def slice012 : Slice := ⟨cell012,8,16⟩
theorem slice012_checked : FastCellPartition.accepts 1 1 4 slice012=true :=
  accepts_of_checks 1 1 4 slice012 cell012_checked (by decide +kernel)
def slice013 : Slice := ⟨cell013,16,32⟩
theorem slice013_checked : FastCellPartition.accepts 1 1 4 slice013=true :=
  accepts_of_checks 1 1 4 slice013 cell013_checked (by decide +kernel)
def slice014 : Slice := ⟨cell014,32,64⟩
theorem slice014_checked : FastCellPartition.accepts 1 1 4 slice014=true :=
  accepts_of_checks 1 1 4 slice014 cell014_checked (by decide +kernel)
def slice015 : Slice := ⟨cell015,64,128⟩
theorem slice015_checked : FastCellPartition.accepts 1 1 4 slice015=true :=
  accepts_of_checks 1 1 4 slice015 cell015_checked (by decide +kernel)
def slice016 : Slice := ⟨cell016,128,256⟩
theorem slice016_checked : FastCellPartition.accepts 1 1 4 slice016=true :=
  accepts_of_checks 1 1 4 slice016 cell016_checked (by decide +kernel)
def slice017 : Slice := ⟨cell017,256,512⟩
theorem slice017_checked : FastCellPartition.accepts 1 1 4 slice017=true :=
  accepts_of_checks 1 1 4 slice017 cell017_checked (by decide +kernel)
def slice018 : Slice := ⟨cell018,512,1024⟩
theorem slice018_checked : FastCellPartition.accepts 1 1 4 slice018=true :=
  accepts_of_checks 1 1 4 slice018 cell018_checked (by decide +kernel)
def partition : List Slice := [slice000,slice001,slice002,slice003,slice004,slice005,slice006,slice007,slice008,slice009,slice010,slice011,slice012,slice013,slice014,slice015,slice016,slice017,slice018]
theorem partition_checked : checkAt 1 1 4 (1/1000) 1024 partition=true := by
  unfold partition
  apply checked_cons _ _ _ _ _ _ _ rfl slice000_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice001_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice002_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice003_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice004_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice005_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice006_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice007_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice008_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice009_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice010_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice011_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice012_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice013_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice014_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice015_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice016_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice017_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice018_checked
  decide +kernel
theorem budget_checked : FastPaidDegreeOneClass.accepts (payment partition)=true := by decide +kernel
noncomputable section
open scoped Classical
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=1) (hq : ArmClasses.classify q=4) :
    (189/5000 : ℝ) < ActualFusionIntegral.normalizedIntegral C u p q 2 :=
  FastPaidDegreeOneClass.normalized_target C u p q hd 1 4 hp hq
    partition partition_checked budget_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end
end Gebendorfer.RadenkovicGutman.DegreeOneFastFullBoxClass20
