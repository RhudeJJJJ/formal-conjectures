/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00075 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 850117536614069950919057866752000000000000 40232640740893215189217999640913248256 218252534265058405187059712000000000000))
theorem leaf00075_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 850117536614069950919057866752000000000000 40232640740893215189217999640913248256 218252534265058405187059712000000000000 raw00075=true := by decide +kernel
#print axioms leaf00075_raw
theorem leaf00075_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00075=true := by decide +kernel
#print axioms leaf00075_rectangular
def affine00075 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00075 (IntegerComputedClassCell.leftNumerator ![(31/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/16000),0,0] ![(1/16000),1,(1/16)]))
theorem leaf00075_transform : affine00075=(NestedInteger.clearedAll 3 raw00075 (IntegerComputedClassCell.leftNumerator ![(31/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/16000),0,0] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00075_transform
theorem leaf00075_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00075=true := by decide +kernel
#print axioms leaf00075_sign
theorem leaf00075_log : RationalLog.accepts (85813/2147483648) (-2718616871/536870912) 15 8=true := by decide +kernel
#print axioms leaf00075_log
def leaf00075 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (184339856013/1000000000000) (85813/2147483648) (-2718616871/536870912) 15 8 ![60,0,4] ![(31/16000),0,0] ![(1/16000),1,(1/16)] affine00075
theorem leaf00075_checked : FastNestedCellData.accepts 1 2 4 leaf00075=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (184339856013/1000000000000) (85813/2147483648) (-2718616871/536870912) 15 8 ![60,0,4] ![(31/16000),0,0] ![(1/16000),1,(1/16)] 850117536614069950919057866752000000000000 40232640740893215189217999640913248256 218252534265058405187059712000000000000 raw00075 affine00075
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00075_raw leaf00075_rectangular
    leaf00075_transform leaf00075_sign leaf00075_log
#print axioms leaf00075_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
