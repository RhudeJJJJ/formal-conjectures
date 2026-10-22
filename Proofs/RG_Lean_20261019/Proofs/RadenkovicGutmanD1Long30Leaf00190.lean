/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00190 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 66743504581907194873510467993600000000000 23701250937855239412538075495249477632 65506136217471425015132979200000000000))
theorem leaf00190_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 66743504581907194873510467993600000000000 23701250937855239412538075495249477632 65506136217471425015132979200000000000 raw00190=true := by decide +kernel
#print axioms leaf00190_raw
theorem leaf00190_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00190=true := by decide +kernel
#print axioms leaf00190_rectangular
def affine00190 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00190 (IntegerComputedClassCell.leftNumerator ![(13/3200),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/3200),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/3200),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00190_transform : affine00190=(NestedInteger.clearedAll 3 raw00190 (IntegerComputedClassCell.leftNumerator ![(13/3200),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/3200),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/3200),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00190_transform
theorem leaf00190_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00190=true := by decide +kernel
#print axioms leaf00190_sign
theorem leaf00190_log : RationalLog.accepts (559981/2147483648) (-4430207581/1073741824) 12 8=true := by decide +kernel
#print axioms leaf00190_log
def leaf00190 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (72363452667/200000000000) (559981/2147483648) (-4430207581/1073741824) 12 8 ![60,0,4] ![(13/3200),0,0] ![(3/32000),1,(1/16)] affine00190
theorem leaf00190_checked : FastNestedCellData.accepts 1 2 4 leaf00190=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (72363452667/200000000000) (559981/2147483648) (-4430207581/1073741824) 12 8 ![60,0,4] ![(13/3200),0,0] ![(3/32000),1,(1/16)] 66743504581907194873510467993600000000000 23701250937855239412538075495249477632 65506136217471425015132979200000000000 raw00190 affine00190
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00190_raw leaf00190_rectangular
    leaf00190_transform leaf00190_sign leaf00190_log
#print axioms leaf00190_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
