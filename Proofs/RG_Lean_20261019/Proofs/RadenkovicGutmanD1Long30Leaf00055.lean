/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00055 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 37281521570683272871075538534400000000000 1196838267176005289555177261028605952 7402383366502293193097216000000000000))
theorem leaf00055_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 37281521570683272871075538534400000000000 1196838267176005289555177261028605952 7402383366502293193097216000000000000 raw00055=true := by decide +kernel
#print axioms leaf00055_raw
theorem leaf00055_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00055=true := by decide +kernel
#print axioms leaf00055_rectangular
def affine00055 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00055 (IntegerComputedClassCell.leftNumerator ![(27/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/16000),0,0] ![(1/16000),1,(1/16)]))
theorem leaf00055_transform : affine00055=(NestedInteger.clearedAll 3 raw00055 (IntegerComputedClassCell.leftNumerator ![(27/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/16000),0,0] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00055_transform
theorem leaf00055_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00055=true := by decide +kernel
#print axioms leaf00055_sign
theorem leaf00055_log : RationalLog.accepts (59345/2147483648) (-22540932639/4294967296) 16 8=true := by decide +kernel
#print axioms leaf00055_log
def leaf00055 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (80841413361/500000000000) (59345/2147483648) (-22540932639/4294967296) 16 8 ![60,0,4] ![(27/16000),0,0] ![(1/16000),1,(1/16)] affine00055
theorem leaf00055_checked : FastNestedCellData.accepts 1 2 4 leaf00055=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (80841413361/500000000000) (59345/2147483648) (-22540932639/4294967296) 16 8 ![60,0,4] ![(27/16000),0,0] ![(1/16000),1,(1/16)] 37281521570683272871075538534400000000000 1196838267176005289555177261028605952 7402383366502293193097216000000000000 raw00055 affine00055
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00055_raw leaf00055_rectangular
    leaf00055_transform leaf00055_sign leaf00055_log
#print axioms leaf00055_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
