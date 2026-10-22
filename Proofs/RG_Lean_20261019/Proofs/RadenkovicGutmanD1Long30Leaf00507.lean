/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00507 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3825875638185421762556554379264000000000000 2435545475047808387619202376251819161550848 11743163737386185231627622285312000000000000))
theorem leaf00507_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3825875638185421762556554379264000000000000 2435545475047808387619202376251819161550848 11743163737386185231627622285312000000000000 raw00507=true := by decide +kernel
#print axioms leaf00507_raw
theorem leaf00507_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00507=true := by decide +kernel
#print axioms leaf00507_rectangular
def affine00507 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00507 (IntegerComputedClassCell.leftNumerator ![(11/800),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/800),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/800),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00507_transform : affine00507=(NestedInteger.clearedAll 3 raw00507 (IntegerComputedClassCell.leftNumerator ![(11/800),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/800),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/800),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00507_transform
theorem leaf00507_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00507=true := by decide +kernel
#print axioms leaf00507_sign
theorem leaf00507_log : RationalLog.accepts (2264507043/4294967296) (-1374576073/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00507_log
def leaf00507 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (207401133929/1000000000000) (2264507043/4294967296) (-1374576073/4294967296) 1 8 ![60,0,4] ![(11/800),0,(1/8)] ![(1/3200),1,(1/8)] affine00507
theorem leaf00507_checked : FastNestedCellData.accepts 1 2 4 leaf00507=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (207401133929/1000000000000) (2264507043/4294967296) (-1374576073/4294967296) 1 8 ![60,0,4] ![(11/800),0,(1/8)] ![(1/3200),1,(1/8)] 3825875638185421762556554379264000000000000 2435545475047808387619202376251819161550848 11743163737386185231627622285312000000000000 raw00507 affine00507
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00507_raw leaf00507_rectangular
    leaf00507_transform leaf00507_sign leaf00507_log
#print axioms leaf00507_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
