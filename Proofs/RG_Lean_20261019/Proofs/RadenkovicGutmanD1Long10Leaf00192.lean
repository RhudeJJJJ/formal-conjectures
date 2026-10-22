/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00192 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 354931125633900099526350340096000000000000 7237315714371167678157150998394954579968 13433683841498239238276120576000000000000))
theorem leaf00192_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 354931125633900099526350340096000000000000 7237315714371167678157150998394954579968 13433683841498239238276120576000000000000 raw00192=true := by decide +kernel
#print axioms leaf00192_raw
theorem leaf00192_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00192=true := by decide +kernel
#print axioms leaf00192_rectangular
def affine00192 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00192 (IntegerComputedClassCell.leftNumerator ![(97/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(97/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(97/3200),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00192_transform : affine00192=(NestedInteger.clearedAll 3 raw00192 (IntegerComputedClassCell.leftNumerator ![(97/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(97/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(97/3200),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00192_transform
theorem leaf00192_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00192=true := by decide +kernel
#print axioms leaf00192_sign
theorem leaf00192_log : RationalLog.accepts (28457513/2147483648) (-580309131/268435456) 7 8=true := by decide +kernel
#print axioms leaf00192_log
def leaf00192 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (538743936493/1000000000000) (28457513/2147483648) (-580309131/268435456) 7 8 ![52,0,4] ![(97/3200),0,0] ![(3/3200),1,(1/4)] affine00192
theorem leaf00192_checked : FastNestedCellData.accepts 1 0 4 leaf00192=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (538743936493/1000000000000) (28457513/2147483648) (-580309131/268435456) 7 8 ![52,0,4] ![(97/3200),0,0] ![(3/3200),1,(1/4)] 354931125633900099526350340096000000000000 7237315714371167678157150998394954579968 13433683841498239238276120576000000000000 raw00192 affine00192
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00192_raw leaf00192_rectangular
    leaf00192_transform leaf00192_sign leaf00192_log
#print axioms leaf00192_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
