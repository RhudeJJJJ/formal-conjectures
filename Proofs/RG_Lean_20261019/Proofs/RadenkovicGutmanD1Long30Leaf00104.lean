/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00104 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 214746917395715583767478272000000000000 210166343217481238412554263735214014464 23506866010242485852458450944000000000000))
theorem leaf00104_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 214746917395715583767478272000000000000 210166343217481238412554263735214014464 23506866010242485852458450944000000000000 raw00104=true := by decide +kernel
#print axioms leaf00104_raw
theorem leaf00104_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00104=true := by decide +kernel
#print axioms leaf00104_rectangular
def affine00104 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00104 (IntegerComputedClassCell.leftNumerator ![(19/8000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/8000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/8000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00104_transform : affine00104=(NestedInteger.clearedAll 3 raw00104 (IntegerComputedClassCell.leftNumerator ![(19/8000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/8000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/8000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00104_transform
theorem leaf00104_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00104=true := by decide +kernel
#print axioms leaf00104_sign
theorem leaf00104_log : RationalLog.accepts (2083053771/2147483648) (-16354055/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00104_log
def leaf00104 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1117579557/125000000000) (2083053771/2147483648) (-16354055/1073741824) 1 8 ![60,0,4] ![(19/8000),0,(1/2)] ![(3/32000),1,(1/2)] affine00104
theorem leaf00104_checked : FastNestedCellData.accepts 1 2 4 leaf00104=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1117579557/125000000000) (2083053771/2147483648) (-16354055/1073741824) 1 8 ![60,0,4] ![(19/8000),0,(1/2)] ![(3/32000),1,(1/2)] 214746917395715583767478272000000000000 210166343217481238412554263735214014464 23506866010242485852458450944000000000000 raw00104 affine00104
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00104_raw leaf00104_rectangular
    leaf00104_transform leaf00104_sign leaf00104_log
#print axioms leaf00104_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
