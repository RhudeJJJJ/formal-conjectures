/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00566 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 8522696706092000855622359711744000000000000 3148944577820772811227503299044532700577792 6815656679162850005514020978688000000000000))
theorem leaf00566_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 8522696706092000855622359711744000000000000 3148944577820772811227503299044532700577792 6815656679162850005514020978688000000000000 raw00566=true := by decide +kernel
#print axioms leaf00566_raw
theorem leaf00566_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00566=true := by decide +kernel
#print axioms leaf00566_rectangular
def affine00566 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00566 (IntegerComputedClassCell.leftNumerator ![(7/400),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/400),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/400),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00566_transform : affine00566=(NestedInteger.clearedAll 3 raw00566 (IntegerComputedClassCell.leftNumerator ![(7/400),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/400),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/400),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00566_transform
theorem leaf00566_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00566=true := by decide +kernel
#print axioms leaf00566_sign
theorem leaf00566_log : RationalLog.accepts (1085414517/4294967296) (-2953825139/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00566_log
def leaf00566 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (462016314209/1000000000000) (1085414517/4294967296) (-2953825139/4294967296) 2 8 ![60,0,4] ![(7/400),0,(1/16)] ![(1/3200),1,(1/16)] affine00566
theorem leaf00566_checked : FastNestedCellData.accepts 1 2 4 leaf00566=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (462016314209/1000000000000) (1085414517/4294967296) (-2953825139/4294967296) 2 8 ![60,0,4] ![(7/400),0,(1/16)] ![(1/3200),1,(1/16)] 8522696706092000855622359711744000000000000 3148944577820772811227503299044532700577792 6815656679162850005514020978688000000000000 raw00566 affine00566
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00566_raw leaf00566_rectangular
    leaf00566_transform leaf00566_sign leaf00566_log
#print axioms leaf00566_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
