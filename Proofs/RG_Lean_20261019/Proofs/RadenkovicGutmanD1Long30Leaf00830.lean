/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00830 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3234751356577723101508315748761600000000000 270774709502281549563294750243906876604416 308828173619261741835151736832000000000000))
theorem leaf00830_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3234751356577723101508315748761600000000000 270774709502281549563294750243906876604416 308828173619261741835151736832000000000000 raw00830=true := by decide +kernel
#print axioms leaf00830_raw
theorem leaf00830_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00830=true := by decide +kernel
#print axioms leaf00830_rectangular
def affine00830 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00830 (IntegerComputedClassCell.leftNumerator ![(77/1600),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(77/1600),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(77/1600),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00830_transform : affine00830=(NestedInteger.clearedAll 3 raw00830 (IntegerComputedClassCell.leftNumerator ![(77/1600),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(77/1600),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(77/1600),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00830_transform
theorem leaf00830_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00830=true := by decide +kernel
#print axioms leaf00830_sign
theorem leaf00830_log : RationalLog.accepts (191563795/4294967296) (-3339313897/2147483648) 5 8=true := by decide +kernel
#print axioms leaf00830_log
def leaf00830 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (876781112063/1000000000000) (191563795/4294967296) (-3339313897/2147483648) 5 8 ![60,0,4] ![(77/1600),0,0] ![(3/3200),1,(1/16)] affine00830
theorem leaf00830_checked : FastNestedCellData.accepts 1 2 4 leaf00830=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (876781112063/1000000000000) (191563795/4294967296) (-3339313897/2147483648) 5 8 ![60,0,4] ![(77/1600),0,0] ![(3/3200),1,(1/16)] 3234751356577723101508315748761600000000000 270774709502281549563294750243906876604416 308828173619261741835151736832000000000000 raw00830 affine00830
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00830_raw leaf00830_rectangular
    leaf00830_transform leaf00830_sign leaf00830_log
#print axioms leaf00830_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
