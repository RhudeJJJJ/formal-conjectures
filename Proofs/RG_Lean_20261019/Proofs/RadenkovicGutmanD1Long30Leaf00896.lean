/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00896 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3366538134306127186525501259776000000000000 954562416681280611645220811950192678928384 1307616897567875019845440372736000000000000))
theorem leaf00896_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3366538134306127186525501259776000000000000 954562416681280611645220811950192678928384 1307616897567875019845440372736000000000000 raw00896=true := by decide +kernel
#print axioms leaf00896_raw
theorem leaf00896_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00896=true := by decide +kernel
#print axioms leaf00896_rectangular
def affine00896 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00896 (IntegerComputedClassCell.leftNumerator ![(43/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(43/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(43/640),0,(1/16)] ![(1/640),1,(1/16)]))
theorem leaf00896_transform : affine00896=(NestedInteger.clearedAll 3 raw00896 (IntegerComputedClassCell.leftNumerator ![(43/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(43/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(43/640),0,(1/16)] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00896_transform
theorem leaf00896_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00896=true := by decide +kernel
#print axioms leaf00896_sign
theorem leaf00896_log : RationalLog.accepts (703937581/4294967296) (-3883744751/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00896_log
def leaf00896 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (365000795897/500000000000) (703937581/4294967296) (-3883744751/4294967296) 3 8 ![60,0,4] ![(43/640),0,(1/16)] ![(1/640),1,(1/16)] affine00896
theorem leaf00896_checked : FastNestedCellData.accepts 1 2 4 leaf00896=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (365000795897/500000000000) (703937581/4294967296) (-3883744751/4294967296) 3 8 ![60,0,4] ![(43/640),0,(1/16)] ![(1/640),1,(1/16)] 3366538134306127186525501259776000000000000 954562416681280611645220811950192678928384 1307616897567875019845440372736000000000000 raw00896 affine00896
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00896_raw leaf00896_rectangular
    leaf00896_transform leaf00896_sign leaf00896_log
#print axioms leaf00896_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
