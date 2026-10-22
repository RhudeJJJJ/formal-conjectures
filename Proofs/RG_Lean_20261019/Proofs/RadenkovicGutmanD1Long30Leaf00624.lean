/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00624 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 221611272278441114101350400000000000 186231580301035014363354015736004608 2365381922547718402814771200000000000))
theorem leaf00624_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 221611272278441114101350400000000000 186231580301035014363354015736004608 2365381922547718402814771200000000000 raw00624=true := by decide +kernel
#print axioms leaf00624_raw
theorem leaf00624_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00624=true := by decide +kernel
#print axioms leaf00624_rectangular
def affine00624 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00624 (IntegerComputedClassCell.leftNumerator ![(137/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(137/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(137/6400),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00624_transform : affine00624=(NestedInteger.clearedAll 3 raw00624 (IntegerComputedClassCell.leftNumerator ![(137/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(137/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(137/6400),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00624_transform
theorem leaf00624_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00624=true := by decide +kernel
#print axioms leaf00624_sign
theorem leaf00624_log : RationalLog.accepts (418232461/536870912) (-16758445/134217728) 1 8=true := by decide +kernel
#print axioms leaf00624_log
def leaf00624 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (246037937/3125000000) (418232461/536870912) (-16758445/134217728) 1 8 ![60,0,4] ![(137/6400),0,(1/2)] ![(3/6400),1,(1/2)] affine00624
theorem leaf00624_checked : FastNestedCellData.accepts 1 2 4 leaf00624=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (246037937/3125000000) (418232461/536870912) (-16758445/134217728) 1 8 ![60,0,4] ![(137/6400),0,(1/2)] ![(3/6400),1,(1/2)] 221611272278441114101350400000000000 186231580301035014363354015736004608 2365381922547718402814771200000000000 raw00624 affine00624
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00624_raw leaf00624_rectangular
    leaf00624_transform leaf00624_sign leaf00624_log
#print axioms leaf00624_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
