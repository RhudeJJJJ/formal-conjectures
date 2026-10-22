/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanPackedIntegerSemanticAffine
import Proofs.RadenkovicGutmanD1Norm00Pack
namespace Gebendorfer.RadenkovicGutman.DegreeOneFast32Control00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem leaf00000_young : (0 : ℚ)<(629387643537/1000000000000) := by decide +kernel
#print axioms leaf00000_young
theorem leaf00000_width : ∀ i : Fin 3, (0 : ℚ)<(![(1/8000),(1/256),(1/256)] : Fin 3 → ℚ) i := by decide +kernel
#print axioms leaf00000_width
theorem leaf00000_raw : PackedIntegerSemanticAffine.rawCheck
    (NormProgramPack.polynomial DegreeOneNormPack00.pack false (629387643537/1000000000000) (12727/536870912))
    (IntegerComputedClassCell.baseScale (629387643537/1000000000000) (12727/536870912)) ![88,4,4]=true := by decide +kernel
#print axioms leaf00000_raw
theorem leaf00000_sign : NestedInteger.bernsteinCheck 3 ![88,4,4]
    (PackedIntegerClassCell.integerAffine DegreeOneNormPack00.pack false (629387643537/1000000000000) (12727/536870912)
      ![88,4,4] ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)])=true := by decide +kernel
#print axioms leaf00000_sign
theorem leaf00000_log : RationalLog.accepts (12727/536870912) (-22870244509/4294967296) 16 8=true := by decide +kernel
#print axioms leaf00000_log
def leaf00000 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack00.pack false (629387643537/1000000000000) (12727/536870912) (-22870244509/4294967296) 16 8 ![88,4,4] ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]
theorem leaf00000_checked : FastNestedCellData.accepts 1 4 4 leaf00000=true :=
  PackedIntegerSemanticAffine.accepts_make DegreeOneNormPack00.pack false (629387643537/1000000000000) (12727/536870912) (-22870244509/4294967296) 16 8 ![88,4,4] ![(1/1000),0,0] ![(1/8000),(1/256),(1/256)]
    leaf00000_young leaf00000_width leaf00000_raw leaf00000_sign leaf00000_log
#print axioms leaf00000_checked
theorem leaf01753_young : (0 : ℚ)<(1571/1000000000000) := by decide +kernel
#print axioms leaf01753_young
theorem leaf01753_width : ∀ i : Fin 3, (0 : ℚ)<(![(1/1024),1,1] : Fin 3 → ℚ) i := by decide +kernel
#print axioms leaf01753_width
theorem leaf01753_raw : PackedIntegerSemanticAffine.rawCheck
    (NormProgramPack.polynomial DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912))
    (IntegerComputedClassCell.baseScale (1571/1000000000000) (536871935/536870912)) ![88,4,4]=true := by decide +kernel
#print axioms leaf01753_raw
theorem leaf01753_sign : NestedInteger.bernsteinCheck 3 ![88,4,4]
    (PackedIntegerClassCell.integerAffine DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912)
      ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1])=true := by decide +kernel
#print axioms leaf01753_sign
theorem leaf01753_log : RationalLog.accepts (536871935/536870912) (4091/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01753_log
def leaf01753 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1]
theorem leaf01753_checked : FastNestedCellData.accepts 1 4 4 leaf01753=true :=
  PackedIntegerSemanticAffine.accepts_make DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1]
    leaf01753_young leaf01753_width leaf01753_raw leaf01753_sign leaf01753_log
#print axioms leaf01753_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFast32Control00
