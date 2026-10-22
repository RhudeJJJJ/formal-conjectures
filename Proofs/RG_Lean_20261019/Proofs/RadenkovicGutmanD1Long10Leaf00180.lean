/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00180 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 144043054921071914388159463424000000000000 2152167384168974026834436711383484596224 4306490271400949746231148544000000000000))
theorem leaf00180_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 144043054921071914388159463424000000000000 2152167384168974026834436711383484596224 4306490271400949746231148544000000000000 raw00180=true := by decide +kernel
#print axioms leaf00180_raw
theorem leaf00180_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00180=true := by decide +kernel
#print axioms leaf00180_rectangular
def affine00180 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00180 (IntegerComputedClassCell.leftNumerator ![(17/640),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/640),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/640),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00180_transform : affine00180=(NestedInteger.clearedAll 3 raw00180 (IntegerComputedClassCell.leftNumerator ![(17/640),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/640),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/640),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00180_transform
theorem leaf00180_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00180=true := by decide +kernel
#print axioms leaf00180_sign
theorem leaf00180_log : RationalLog.accepts (10697069/1073741824) (-4948806483/2147483648) 7 8=true := by decide +kernel
#print axioms leaf00180_log
def leaf00180 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (249874868923/500000000000) (10697069/1073741824) (-4948806483/2147483648) 7 8 ![52,0,4] ![(17/640),0,0] ![(3/3200),1,(1/4)] affine00180
theorem leaf00180_checked : FastNestedCellData.accepts 1 0 4 leaf00180=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (249874868923/500000000000) (10697069/1073741824) (-4948806483/2147483648) 7 8 ![52,0,4] ![(17/640),0,0] ![(3/3200),1,(1/4)] 144043054921071914388159463424000000000000 2152167384168974026834436711383484596224 4306490271400949746231148544000000000000 raw00180 affine00180
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00180_raw leaf00180_rectangular
    leaf00180_transform leaf00180_sign leaf00180_log
#print axioms leaf00180_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
