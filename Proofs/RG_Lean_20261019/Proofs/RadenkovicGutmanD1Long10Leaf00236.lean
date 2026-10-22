/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00236 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 175084825906893258552502124544000000000000 128877291181964548064971880157779941392384 848648074951853084932975886336000000000000))
theorem leaf00236_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 175084825906893258552502124544000000000000 128877291181964548064971880157779941392384 848648074951853084932975886336000000000000 raw00236=true := by decide +kernel
#print axioms leaf00236_raw
theorem leaf00236_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00236=true := by decide +kernel
#print axioms leaf00236_rectangular
def affine00236 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00236 (IntegerComputedClassCell.leftNumerator ![(139/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(139/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(139/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00236_transform : affine00236=(NestedInteger.clearedAll 3 raw00236 (IntegerComputedClassCell.leftNumerator ![(139/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(139/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(139/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00236_transform
theorem leaf00236_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00236=true := by decide +kernel
#print axioms leaf00236_sign
theorem leaf00236_log : RationalLog.accepts (1372326187/2147483648) (-480810347/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00236_log
def leaf00236 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (75930939447/500000000000) (1372326187/2147483648) (-480810347/2147483648) 1 8 ![52,0,4] ![(139/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00236
theorem leaf00236_checked : FastNestedCellData.accepts 1 0 4 leaf00236=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (75930939447/500000000000) (1372326187/2147483648) (-480810347/2147483648) 1 8 ![52,0,4] ![(139/3200),0,(1/2)] ![(3/3200),1,(1/2)] 175084825906893258552502124544000000000000 128877291181964548064971880157779941392384 848648074951853084932975886336000000000000 raw00236 affine00236
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00236_raw leaf00236_rectangular
    leaf00236_transform leaf00236_sign leaf00236_log
#print axioms leaf00236_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
