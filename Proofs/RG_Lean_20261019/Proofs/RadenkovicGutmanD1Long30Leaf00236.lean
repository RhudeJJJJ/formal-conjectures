/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00236 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 353988171869422498234215956480000000000 250926135255389741745248540769057243136 1634507367158810469231650406400000000000))
theorem leaf00236_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 353988171869422498234215956480000000000 250926135255389741745248540769057243136 1634507367158810469231650406400000000000 raw00236=true := by decide +kernel
#print axioms leaf00236_raw
theorem leaf00236_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00236=true := by decide +kernel
#print axioms leaf00236_rectangular
def affine00236 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00236 (IntegerComputedClassCell.leftNumerator ![(157/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(157/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(157/32000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00236_transform : affine00236=(NestedInteger.clearedAll 3 raw00236 (IntegerComputedClassCell.leftNumerator ![(157/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(157/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(157/32000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00236_transform
theorem leaf00236_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00236=true := by decide +kernel
#print axioms leaf00236_sign
theorem leaf00236_log : RationalLog.accepts (659830945/1073741824) (-130706919/536870912) 1 8=true := by decide +kernel
#print axioms leaf00236_log
def leaf00236 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (15351789799/100000000000) (659830945/1073741824) (-130706919/536870912) 1 8 ![60,0,4] ![(157/32000),0,(1/16)] ![(3/32000),1,(1/16)] affine00236
theorem leaf00236_checked : FastNestedCellData.accepts 1 2 4 leaf00236=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (15351789799/100000000000) (659830945/1073741824) (-130706919/536870912) 1 8 ![60,0,4] ![(157/32000),0,(1/16)] ![(3/32000),1,(1/16)] 353988171869422498234215956480000000000 250926135255389741745248540769057243136 1634507367158810469231650406400000000000 raw00236 affine00236
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00236_raw leaf00236_rectangular
    leaf00236_transform leaf00236_sign leaf00236_log
#print axioms leaf00236_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
