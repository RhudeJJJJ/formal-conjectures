/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00349 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 247832207887147973893685248000000000000 158643574901005939056401549795631562752 320318488823082642158125056000000000000))
theorem leaf00349_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 247832207887147973893685248000000000000 158643574901005939056401549795631562752 320318488823082642158125056000000000000 raw00349=true := by decide +kernel
#print axioms leaf00349_raw
theorem leaf00349_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00349=true := by decide +kernel
#print axioms leaf00349_rectangular
def affine00349 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00349 (IntegerComputedClassCell.leftNumerator ![(13/80),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/80),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/80),0,(1/4)] ![(1/80),1,(1/4)]))
theorem leaf00349_transform : affine00349=(NestedInteger.clearedAll 3 raw00349 (IntegerComputedClassCell.leftNumerator ![(13/80),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/80),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/80),0,(1/4)] ![(1/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00349_transform
theorem leaf00349_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00349=true := by decide +kernel
#print axioms leaf00349_sign
theorem leaf00349_log : RationalLog.accepts (459669303/1073741824) (-1821919903/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00349_log
def leaf00349 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (30954265137/62500000000) (459669303/1073741824) (-1821919903/4294967296) 2 8 ![52,0,4] ![(13/80),0,(1/4)] ![(1/80),1,(1/4)] affine00349
theorem leaf00349_checked : FastNestedCellData.accepts 1 0 4 leaf00349=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (30954265137/62500000000) (459669303/1073741824) (-1821919903/4294967296) 2 8 ![52,0,4] ![(13/80),0,(1/4)] ![(1/80),1,(1/4)] 247832207887147973893685248000000000000 158643574901005939056401549795631562752 320318488823082642158125056000000000000 raw00349 affine00349
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00349_raw leaf00349_rectangular
    leaf00349_transform leaf00349_sign leaf00349_log
#print axioms leaf00349_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
