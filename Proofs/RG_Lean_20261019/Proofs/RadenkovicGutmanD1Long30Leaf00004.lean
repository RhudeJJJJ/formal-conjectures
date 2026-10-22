/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00004 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 274363847518694267565375488000000000000 271790884428816158790031962031446294528 71381843455328394386463522816000000000000))
theorem leaf00004_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 274363847518694267565375488000000000000 271790884428816158790031962031446294528 71381843455328394386463522816000000000000 raw00004=true := by decide +kernel
#print axioms leaf00004_raw
theorem leaf00004_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00004=true := by decide +kernel
#print axioms leaf00004_rectangular
def affine00004 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00004 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/1000),0,(1/2)] ![(1/16000),1,(1/2)]))
theorem leaf00004_transform : affine00004=(NestedInteger.clearedAll 3 raw00004 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/1000),0,(1/2)] ![(1/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00004_transform
theorem leaf00004_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00004=true := by decide +kernel
#print axioms leaf00004_sign
theorem leaf00004_log : RationalLog.accepts (529818859/536870912) (-1774697/268435456) 1 8=true := by decide +kernel
#print axioms leaf00004_log
def leaf00004 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1903781629/500000000000) (529818859/536870912) (-1774697/268435456) 1 8 ![60,0,4] ![(1/1000),0,(1/2)] ![(1/16000),1,(1/2)] affine00004
theorem leaf00004_checked : FastNestedCellData.accepts 1 2 4 leaf00004=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1903781629/500000000000) (529818859/536870912) (-1774697/268435456) 1 8 ![60,0,4] ![(1/1000),0,(1/2)] ![(1/16000),1,(1/2)] 274363847518694267565375488000000000000 271790884428816158790031962031446294528 71381843455328394386463522816000000000000 raw00004 affine00004
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00004_raw leaf00004_rectangular
    leaf00004_transform leaf00004_sign leaf00004_log
#print axioms leaf00004_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
