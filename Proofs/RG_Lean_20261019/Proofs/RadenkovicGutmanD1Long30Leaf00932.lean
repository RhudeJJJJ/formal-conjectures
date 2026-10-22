/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00932 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2752799156884094310226851790848000000000000 1135598713274442247108589781625436809199616 1902436178627607970865079123968000000000000))
theorem leaf00932_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2752799156884094310226851790848000000000000 1135598713274442247108589781625436809199616 1902436178627607970865079123968000000000000 raw00932=true := by decide +kernel
#print axioms leaf00932_raw
theorem leaf00932_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00932=true := by decide +kernel
#print axioms leaf00932_rectangular
def affine00932 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00932 (IntegerComputedClassCell.leftNumerator ![(27/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(27/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(27/320),0,(1/8)] ![(1/320),1,(1/8)]))
theorem leaf00932_transform : affine00932=(NestedInteger.clearedAll 3 raw00932 (IntegerComputedClassCell.leftNumerator ![(27/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(27/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(27/320),0,(1/8)] ![(1/320),1,(1/8)])) := by decide +kernel
#print axioms leaf00932_transform
theorem leaf00932_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00932=true := by decide +kernel
#print axioms leaf00932_sign
theorem leaf00932_log : RationalLog.accepts (1109500661/4294967296) (-2906691949/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00932_log
def leaf00932 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (298459082631/500000000000) (1109500661/4294967296) (-2906691949/4294967296) 2 8 ![60,0,4] ![(27/320),0,(1/8)] ![(1/320),1,(1/8)] affine00932
theorem leaf00932_checked : FastNestedCellData.accepts 1 2 4 leaf00932=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (298459082631/500000000000) (1109500661/4294967296) (-2906691949/4294967296) 2 8 ![60,0,4] ![(27/320),0,(1/8)] ![(1/320),1,(1/8)] 2752799156884094310226851790848000000000000 1135598713274442247108589781625436809199616 1902436178627607970865079123968000000000000 raw00932 affine00932
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00932_raw leaf00932_rectangular
    leaf00932_transform leaf00932_sign leaf00932_log
#print axioms leaf00932_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
