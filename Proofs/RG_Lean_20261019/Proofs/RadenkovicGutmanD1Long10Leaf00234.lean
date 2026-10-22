/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00234 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 728069394922332880642932473856000000000000 33290017769573107081433795058522818347008 52715823028626529189435015168000000000000))
theorem leaf00234_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 728069394922332880642932473856000000000000 33290017769573107081433795058522818347008 52715823028626529189435015168000000000000 raw00234=true := by decide +kernel
#print axioms leaf00234_raw
theorem leaf00234_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00234=true := by decide +kernel
#print axioms leaf00234_rectangular
def affine00234 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00234 (IntegerComputedClassCell.leftNumerator ![(139/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(139/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(139/3200),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00234_transform : affine00234=(NestedInteger.clearedAll 3 raw00234 (IntegerComputedClassCell.leftNumerator ![(139/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(139/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(139/3200),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00234_transform
theorem leaf00234_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00234=true := by decide +kernel
#print axioms leaf00234_sign
theorem leaf00234_log : RationalLog.accepts (120368863/4294967296) (-7676477581/4294967296) 6 8=true := by decide +kernel
#print axioms leaf00234_log
def leaf00234 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (157874883939/250000000000) (120368863/4294967296) (-7676477581/4294967296) 6 8 ![52,0,4] ![(139/3200),0,0] ![(3/3200),1,(1/4)] affine00234
theorem leaf00234_checked : FastNestedCellData.accepts 1 0 4 leaf00234=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (157874883939/250000000000) (120368863/4294967296) (-7676477581/4294967296) 6 8 ![52,0,4] ![(139/3200),0,0] ![(3/3200),1,(1/4)] 728069394922332880642932473856000000000000 33290017769573107081433795058522818347008 52715823028626529189435015168000000000000 raw00234 affine00234
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00234_raw leaf00234_rectangular
    leaf00234_transform leaf00234_sign leaf00234_log
#print axioms leaf00234_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
