/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00293 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 67460218277788844816133521408000000000000 44858459023886238346913823123788607258624 191662150644091768117691154432000000000000))
theorem leaf00293_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 67460218277788844816133521408000000000000 44858459023886238346913823123788607258624 191662150644091768117691154432000000000000 raw00293=true := by decide +kernel
#print axioms leaf00293_raw
theorem leaf00293_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00293=true := by decide +kernel
#print axioms leaf00293_rectangular
def affine00293 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00293 (IntegerComputedClassCell.leftNumerator ![(23/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/320),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00293_transform : affine00293=(NestedInteger.clearedAll 3 raw00293 (IntegerComputedClassCell.leftNumerator ![(23/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/320),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00293_transform
theorem leaf00293_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00293=true := by decide +kernel
#print axioms leaf00293_sign
theorem leaf00293_log : RationalLog.accepts (578580571/1073741824) (-1327847257/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00293_log
def leaf00293 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (117024824341/500000000000) (578580571/1073741824) (-1327847257/4294967296) 1 8 ![52,0,4] ![(23/320),0,(1/2)] ![(1/320),1,(1/2)] affine00293
theorem leaf00293_checked : FastNestedCellData.accepts 1 0 4 leaf00293=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (117024824341/500000000000) (578580571/1073741824) (-1327847257/4294967296) 1 8 ![52,0,4] ![(23/320),0,(1/2)] ![(1/320),1,(1/2)] 67460218277788844816133521408000000000000 44858459023886238346913823123788607258624 191662150644091768117691154432000000000000 raw00293 affine00293
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00293_raw leaf00293_rectangular
    leaf00293_transform leaf00293_sign leaf00293_log
#print axioms leaf00293_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
