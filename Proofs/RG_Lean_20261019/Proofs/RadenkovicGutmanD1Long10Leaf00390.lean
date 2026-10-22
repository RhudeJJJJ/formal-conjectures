/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00390 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1189090363948921655422825267200000000000 1512907829890475440815810100571198717952 6112038890019593024788496384000000000000))
theorem leaf00390_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1189090363948921655422825267200000000000 1512907829890475440815810100571198717952 6112038890019593024788496384000000000000 raw00390=true := by decide +kernel
#print axioms leaf00390_raw
theorem leaf00390_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00390=true := by decide +kernel
#print axioms leaf00390_rectangular
def affine00390 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00390 (IntegerComputedClassCell.leftNumerator ![(9/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/16),0,0] ![(1/16),1,(1/2)]))
theorem leaf00390_transform : affine00390=(NestedInteger.clearedAll 3 raw00390 (IntegerComputedClassCell.leftNumerator ![(9/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/16),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf00390_transform
theorem leaf00390_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00390=true := by decide +kernel
#print axioms leaf00390_sign
theorem leaf00390_log : RationalLog.accepts (2190164685/2147483648) (42262433/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00390_log
def leaf00390 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (30941144541/125000000000) (2190164685/2147483648) (42262433/4294967296) 0 8 ![52,0,4] ![(9/16),0,0] ![(1/16),1,(1/2)] affine00390
theorem leaf00390_checked : FastNestedCellData.accepts 1 0 4 leaf00390=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (30941144541/125000000000) (2190164685/2147483648) (42262433/4294967296) 0 8 ![52,0,4] ![(9/16),0,0] ![(1/16),1,(1/2)] 1189090363948921655422825267200000000000 1512907829890475440815810100571198717952 6112038890019593024788496384000000000000 raw00390 affine00390
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00390_raw leaf00390_rectangular
    leaf00390_transform leaf00390_sign leaf00390_log
#print axioms leaf00390_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
