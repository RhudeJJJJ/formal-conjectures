/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00332 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 372071608988030678901853257728000000000000 245908490907855958250002880833660813049856 761985543869338578122547658752000000000000))
theorem leaf00332_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 372071608988030678901853257728000000000000 245908490907855958250002880833660813049856 761985543869338578122547658752000000000000 raw00332=true := by decide +kernel
#print axioms leaf00332_raw
theorem leaf00332_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00332=true := by decide +kernel
#print axioms leaf00332_rectangular
def affine00332 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00332 (IntegerComputedClassCell.leftNumerator ![(19/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/160),0,(1/2)] ![(1/160),1,(1/2)]))
theorem leaf00332_transform : affine00332=(NestedInteger.clearedAll 3 raw00332 (IntegerComputedClassCell.leftNumerator ![(19/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/160),0,(1/2)] ![(1/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00332_transform
theorem leaf00332_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00332=true := by decide +kernel
#print axioms leaf00332_sign
theorem leaf00332_log : RationalLog.accepts (2146044439/4294967296) (-1489962001/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00332_log
def leaf00332 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (80680169357/250000000000) (2146044439/4294967296) (-1489962001/4294967296) 2 8 ![52,0,4] ![(19/160),0,(1/2)] ![(1/160),1,(1/2)] affine00332
theorem leaf00332_checked : FastNestedCellData.accepts 1 0 4 leaf00332=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (80680169357/250000000000) (2146044439/4294967296) (-1489962001/4294967296) 2 8 ![52,0,4] ![(19/160),0,(1/2)] ![(1/160),1,(1/2)] 372071608988030678901853257728000000000000 245908490907855958250002880833660813049856 761985543869338578122547658752000000000000 raw00332 affine00332
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00332_raw leaf00332_rectangular
    leaf00332_transform leaf00332_sign leaf00332_log
#print axioms leaf00332_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
