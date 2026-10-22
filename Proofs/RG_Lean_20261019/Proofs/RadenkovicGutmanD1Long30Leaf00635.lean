/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00635 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1309891278149959264599688609792000000000000 25143341591872571083065418197831203684352 29507079152286708305345118208000000000000))
theorem leaf00635_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1309891278149959264599688609792000000000000 25143341591872571083065418197831203684352 29507079152286708305345118208000000000000 raw00635=true := by decide +kernel
#print axioms leaf00635_raw
theorem leaf00635_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00635=true := by decide +kernel
#print axioms leaf00635_rectangular
def affine00635 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00635 (IntegerComputedClassCell.leftNumerator ![(73/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(73/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(73/3200),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00635_transform : affine00635=(NestedInteger.clearedAll 3 raw00635 (IntegerComputedClassCell.leftNumerator ![(73/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(73/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(73/3200),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00635_transform
theorem leaf00635_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00635=true := by decide +kernel
#print axioms leaf00635_sign
theorem leaf00635_log : RationalLog.accepts (44512329/4294967296) (-9812782923/4294967296) 7 8=true := by decide +kernel
#print axioms leaf00635_log
def leaf00635 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (426056090847/500000000000) (44512329/4294967296) (-9812782923/4294967296) 7 8 ![60,0,4] ![(73/3200),0,0] ![(3/6400),1,(1/16)] affine00635
theorem leaf00635_checked : FastNestedCellData.accepts 1 2 4 leaf00635=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (426056090847/500000000000) (44512329/4294967296) (-9812782923/4294967296) 7 8 ![60,0,4] ![(73/3200),0,0] ![(3/6400),1,(1/16)] 1309891278149959264599688609792000000000000 25143341591872571083065418197831203684352 29507079152286708305345118208000000000000 raw00635 affine00635
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00635_raw leaf00635_rectangular
    leaf00635_transform leaf00635_sign leaf00635_log
#print axioms leaf00635_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
