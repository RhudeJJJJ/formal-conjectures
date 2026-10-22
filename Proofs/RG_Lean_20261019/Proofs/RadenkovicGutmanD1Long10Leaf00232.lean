/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00232 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 66457986882251286149847213670400000000000 38053521879958511789224160285782196617216 132031455539464383524931371008000000000000))
theorem leaf00232_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 66457986882251286149847213670400000000000 38053521879958511789224160285782196617216 132031455539464383524931371008000000000000 raw00232=true := by decide +kernel
#print axioms leaf00232_raw
theorem leaf00232_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00232=true := by decide +kernel
#print axioms leaf00232_rectangular
def affine00232 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00232 (IntegerComputedClassCell.leftNumerator ![(17/400),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/400),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/400),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00232_transform : affine00232=(NestedInteger.clearedAll 3 raw00232 (IntegerComputedClassCell.leftNumerator ![(17/400),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/400),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/400),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00232_transform
theorem leaf00232_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00232=true := by decide +kernel
#print axioms leaf00232_sign
theorem leaf00232_log : RationalLog.accepts (477264355/1073741824) (-870626755/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00232_log
def leaf00232 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (288215575027/1000000000000) (477264355/1073741824) (-870626755/2147483648) 2 8 ![52,0,4] ![(17/400),0,(1/4)] ![(3/3200),1,(1/4)] affine00232
theorem leaf00232_checked : FastNestedCellData.accepts 1 0 4 leaf00232=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (288215575027/1000000000000) (477264355/1073741824) (-870626755/2147483648) 2 8 ![52,0,4] ![(17/400),0,(1/4)] ![(3/3200),1,(1/4)] 66457986882251286149847213670400000000000 38053521879958511789224160285782196617216 132031455539464383524931371008000000000000 raw00232 affine00232
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00232_raw leaf00232_rectangular
    leaf00232_transform leaf00232_sign leaf00232_log
#print axioms leaf00232_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
