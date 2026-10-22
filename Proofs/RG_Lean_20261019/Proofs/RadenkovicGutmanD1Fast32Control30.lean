/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanPackedIntegerSemanticAffine
import Proofs.RadenkovicGutmanD1Norm30Pack
namespace Gebendorfer.RadenkovicGutman.DegreeOneFast32Control30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem leaf00000_young : (0 : ℚ)<(48977026691/500000000000) := by decide +kernel
#print axioms leaf00000_young
theorem leaf00000_width : ∀ i : Fin 3, (0 : ℚ)<(![(1/16000),1,(1/16)] : Fin 3 → ℚ) i := by decide +kernel
#print axioms leaf00000_width
theorem leaf00000_raw : PackedIntegerSemanticAffine.rawCheck
    (NormProgramPack.polynomial DegreeOneNormPack30.pack false (48977026691/500000000000) (7067/1073741824))
    (IntegerComputedClassCell.baseScale (48977026691/500000000000) (7067/1073741824)) ![60,0,4]=true := by decide +kernel
#print axioms leaf00000_raw
theorem leaf00000_sign : NestedInteger.bernsteinCheck 3 ![60,0,4]
    (PackedIntegerClassCell.integerAffine DegreeOneNormPack30.pack false (48977026691/500000000000) (7067/1073741824)
      ![60,0,4] ![(1/1000),0,0] ![(1/16000),1,(1/16)])=true := by decide +kernel
#print axioms leaf00000_sign
theorem leaf00000_log : RationalLog.accepts (7067/1073741824) (-25622109239/4294967296) 18 8=true := by decide +kernel
#print axioms leaf00000_log
def leaf00000 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack30.pack false (48977026691/500000000000) (7067/1073741824) (-25622109239/4294967296) 18 8 ![60,0,4] ![(1/1000),0,0] ![(1/16000),1,(1/16)]
theorem leaf00000_checked : FastNestedCellData.accepts 1 2 4 leaf00000=true :=
  PackedIntegerSemanticAffine.accepts_make DegreeOneNormPack30.pack false (48977026691/500000000000) (7067/1073741824) (-25622109239/4294967296) 18 8 ![60,0,4] ![(1/1000),0,0] ![(1/16000),1,(1/16)]
    leaf00000_young leaf00000_width leaf00000_raw leaf00000_sign leaf00000_log
#print axioms leaf00000_checked
theorem leaf01365_young : (0 : ℚ)<(909/1000000000000) := by decide +kernel
#print axioms leaf01365_young
theorem leaf01365_width : ∀ i : Fin 3, (0 : ℚ)<(![(1/2048),1,1] : Fin 3 → ℚ) i := by decide +kernel
#print axioms leaf01365_width
theorem leaf01365_raw : PackedIntegerSemanticAffine.rawCheck
    (NormProgramPack.polynomial DegreeOneNormPack30.pack true (909/1000000000000) (4294975483/4294967296))
    (IntegerComputedClassCell.baseScale (909/1000000000000) (4294975483/4294967296)) ![60,0,4]=true := by decide +kernel
#print axioms leaf01365_raw
theorem leaf01365_sign : NestedInteger.bernsteinCheck 3 ![60,0,4]
    (PackedIntegerClassCell.integerAffine DegreeOneNormPack30.pack true (909/1000000000000) (4294975483/4294967296)
      ![60,0,4] ![(1/1024),0,0] ![(1/2048),1,1])=true := by decide +kernel
#print axioms leaf01365_sign
theorem leaf01365_log : RationalLog.accepts (4294975483/4294967296) (4093/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01365_log
def leaf01365 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack30.pack true (909/1000000000000) (4294975483/4294967296) (4093/4294967296) 0 8 ![60,0,4] ![(1/1024),0,0] ![(1/2048),1,1]
theorem leaf01365_checked : FastNestedCellData.accepts 1 2 4 leaf01365=true :=
  PackedIntegerSemanticAffine.accepts_make DegreeOneNormPack30.pack true (909/1000000000000) (4294975483/4294967296) (4093/4294967296) 0 8 ![60,0,4] ![(1/1024),0,0] ![(1/2048),1,1]
    leaf01365_young leaf01365_width leaf01365_raw leaf01365_sign leaf01365_log
#print axioms leaf01365_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFast32Control30
