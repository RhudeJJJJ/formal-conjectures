/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00142 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 838513966316697022237719396352000000000000 620296560433401233049853592862826300440576 4548702569769553986246028558336000000000000))
theorem leaf00142_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 838513966316697022237719396352000000000000 620296560433401233049853592862826300440576 4548702569769553986246028558336000000000000 raw00142=true := by decide +kernel
#print axioms leaf00142_raw
theorem leaf00142_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00142=true := by decide +kernel
#print axioms leaf00142_rectangular
def affine00142 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00142 (IntegerComputedClassCell.leftNumerator ![(29/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/1600),0,(1/4)] ![(1/1600),1,(1/4)]))
theorem leaf00142_transform : affine00142=(NestedInteger.clearedAll 3 raw00142 (IntegerComputedClassCell.leftNumerator ![(29/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/1600),0,(1/4)] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00142_transform
theorem leaf00142_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00142=true := by decide +kernel
#print axioms leaf00142_sign
theorem leaf00142_log : RationalLog.accepts (2795953953/4294967296) (-921851599/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00142_log
def leaf00142 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (136367799591/1000000000000) (2795953953/4294967296) (-921851599/4294967296) 1 8 ![52,0,4] ![(29/1600),0,(1/4)] ![(1/1600),1,(1/4)] affine00142
theorem leaf00142_checked : FastNestedCellData.accepts 1 0 4 leaf00142=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (136367799591/1000000000000) (2795953953/4294967296) (-921851599/4294967296) 1 8 ![52,0,4] ![(29/1600),0,(1/4)] ![(1/1600),1,(1/4)] 838513966316697022237719396352000000000000 620296560433401233049853592862826300440576 4548702569769553986246028558336000000000000 raw00142 affine00142
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00142_raw leaf00142_rectangular
    leaf00142_transform leaf00142_sign leaf00142_log
#print axioms leaf00142_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
