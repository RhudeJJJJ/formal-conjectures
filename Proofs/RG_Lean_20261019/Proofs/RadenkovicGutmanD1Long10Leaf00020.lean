/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00020 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 10348391127808781241406193664000000000000 10115799044229450740866316102120534704128 1127008257644301521903159345152000000000000))
theorem leaf00020_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 10348391127808781241406193664000000000000 10115799044229450740866316102120534704128 1127008257644301521903159345152000000000000 raw00020=true := by decide +kernel
#print axioms leaf00020_raw
theorem leaf00020_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00020=true := by decide +kernel
#print axioms leaf00020_rectangular
def affine00020 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00020 (IntegerComputedClassCell.leftNumerator ![(19/8000),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/8000),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/8000),0,(1/2)] ![(3/16000),1,(1/2)]))
theorem leaf00020_transform : affine00020=(NestedInteger.clearedAll 3 raw00020 (IntegerComputedClassCell.leftNumerator ![(19/8000),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/8000),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/8000),0,(1/2)] ![(3/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00020_transform
theorem leaf00020_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00020=true := by decide +kernel
#print axioms leaf00020_sign
theorem leaf00020_log : RationalLog.accepts (2080541939/2147483648) (-68007307/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00020_log
def leaf00020 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (4487899257/500000000000) (2080541939/2147483648) (-68007307/4294967296) 1 8 ![52,0,4] ![(19/8000),0,(1/2)] ![(3/16000),1,(1/2)] affine00020
theorem leaf00020_checked : FastNestedCellData.accepts 1 0 4 leaf00020=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (4487899257/500000000000) (2080541939/2147483648) (-68007307/4294967296) 1 8 ![52,0,4] ![(19/8000),0,(1/2)] ![(3/16000),1,(1/2)] 10348391127808781241406193664000000000000 10115799044229450740866316102120534704128 1127008257644301521903159345152000000000000 raw00020 affine00020
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00020_raw leaf00020_rectangular
    leaf00020_transform leaf00020_sign leaf00020_log
#print axioms leaf00020_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
