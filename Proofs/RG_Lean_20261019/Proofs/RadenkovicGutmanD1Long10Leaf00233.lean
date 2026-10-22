/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00233 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 9036673547738156462478721024000000000000 6681400328921514961216946453062099140608 44864728034733289780929363968000000000000))
theorem leaf00233_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 9036673547738156462478721024000000000000 6681400328921514961216946453062099140608 44864728034733289780929363968000000000000 raw00233=true := by decide +kernel
#print axioms leaf00233_raw
theorem leaf00233_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00233=true := by decide +kernel
#print axioms leaf00233_rectangular
def affine00233 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00233 (IntegerComputedClassCell.leftNumerator ![(17/400),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/400),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/400),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00233_transform : affine00233=(NestedInteger.clearedAll 3 raw00233 (IntegerComputedClassCell.leftNumerator ![(17/400),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/400),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/400),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00233_transform
theorem leaf00233_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00233=true := by decide +kernel
#print axioms leaf00233_sign
theorem leaf00233_log : RationalLog.accepts (1381967261/2147483648) (-946586615/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00233_log
def leaf00233 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (74461616303/500000000000) (1381967261/2147483648) (-946586615/4294967296) 1 8 ![52,0,4] ![(17/400),0,(1/2)] ![(3/3200),1,(1/2)] affine00233
theorem leaf00233_checked : FastNestedCellData.accepts 1 0 4 leaf00233=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (74461616303/500000000000) (1381967261/2147483648) (-946586615/4294967296) 1 8 ![52,0,4] ![(17/400),0,(1/2)] ![(3/3200),1,(1/2)] 9036673547738156462478721024000000000000 6681400328921514961216946453062099140608 44864728034733289780929363968000000000000 raw00233 affine00233
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00233_raw leaf00233_rectangular
    leaf00233_transform leaf00233_sign leaf00233_log
#print axioms leaf00233_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
