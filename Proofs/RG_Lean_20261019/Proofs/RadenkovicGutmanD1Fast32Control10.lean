/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanPackedIntegerSemanticAffine
import Proofs.RadenkovicGutmanD1Norm10Pack
namespace Gebendorfer.RadenkovicGutman.DegreeOneFast32Control10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem leaf00406_young : (0 : ℚ)<(29096676651/250000000000) := by decide +kernel
#print axioms leaf00406_young
theorem leaf00406_width : ∀ i : Fin 3, (0 : ℚ)<(![(1/8),1,(1/4)] : Fin 3 → ℚ) i := by decide +kernel
#print axioms leaf00406_width
theorem leaf00406_raw : PackedIntegerSemanticAffine.rawCheck
    (NormProgramPack.polynomial DegreeOneNormPack10.pack true (29096676651/250000000000) (5296067311/4294967296))
    (IntegerComputedClassCell.baseScale (29096676651/250000000000) (5296067311/4294967296)) ![52,0,4]=true := by decide +kernel
#print axioms leaf00406_raw
theorem leaf00406_sign : NestedInteger.bernsteinCheck 3 ![52,0,4]
    (PackedIntegerClassCell.integerAffine DegreeOneNormPack10.pack true (29096676651/250000000000) (5296067311/4294967296)
      ![52,0,4] ![(7/8),0,(1/2)] ![(1/8),1,(1/4)])=true := by decide +kernel
#print axioms leaf00406_sign
theorem leaf00406_log : RationalLog.accepts (5296067311/4294967296) (449942035/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00406_log
def leaf00406 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack10.pack true (29096676651/250000000000) (5296067311/4294967296) (449942035/4294967296) 0 8 ![52,0,4] ![(7/8),0,(1/2)] ![(1/8),1,(1/4)]
theorem leaf00406_checked : FastNestedCellData.accepts 1 0 4 leaf00406=true :=
  PackedIntegerSemanticAffine.accepts_make DegreeOneNormPack10.pack true (29096676651/250000000000) (5296067311/4294967296) (449942035/4294967296) 0 8 ![52,0,4] ![(7/8),0,(1/2)] ![(1/8),1,(1/4)]
    leaf00406_young leaf00406_width leaf00406_raw leaf00406_sign leaf00406_log
#print axioms leaf00406_checked
theorem leaf00407_young : (0 : ℚ)<(58087105111/500000000000) := by decide +kernel
#print axioms leaf00407_young
theorem leaf00407_width : ∀ i : Fin 3, (0 : ℚ)<(![(1/8),1,(1/4)] : Fin 3 → ℚ) i := by decide +kernel
#print axioms leaf00407_width
theorem leaf00407_raw : PackedIntegerSemanticAffine.rawCheck
    (NormProgramPack.polynomial DegreeOneNormPack10.pack true (58087105111/500000000000) (5292682637/4294967296))
    (IntegerComputedClassCell.baseScale (58087105111/500000000000) (5292682637/4294967296)) ![52,0,4]=true := by decide +kernel
#print axioms leaf00407_raw
theorem leaf00407_sign : NestedInteger.bernsteinCheck 3 ![52,0,4]
    (PackedIntegerClassCell.integerAffine DegreeOneNormPack10.pack true (58087105111/500000000000) (5292682637/4294967296)
      ![52,0,4] ![(7/8),0,(3/4)] ![(1/8),1,(1/4)])=true := by decide +kernel
#print axioms leaf00407_sign
theorem leaf00407_log : RationalLog.accepts (5292682637/4294967296) (448569157/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00407_log
def leaf00407 : FastNestedCellData.Cell := PackedIntegerClassCell.make DegreeOneNormPack10.pack true (58087105111/500000000000) (5292682637/4294967296) (448569157/4294967296) 0 8 ![52,0,4] ![(7/8),0,(3/4)] ![(1/8),1,(1/4)]
theorem leaf00407_checked : FastNestedCellData.accepts 1 0 4 leaf00407=true :=
  PackedIntegerSemanticAffine.accepts_make DegreeOneNormPack10.pack true (58087105111/500000000000) (5292682637/4294967296) (448569157/4294967296) 0 8 ![52,0,4] ![(7/8),0,(3/4)] ![(1/8),1,(1/4)]
    leaf00407_young leaf00407_width leaf00407_raw leaf00407_sign leaf00407_log
#print axioms leaf00407_checked
end Gebendorfer.RadenkovicGutman.DegreeOneFast32Control10
