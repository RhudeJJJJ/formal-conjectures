/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00169 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 31320763322353527373766747750400000000000 21675050635587713323445147521694180573184 127657844013661630578046900633600000000000))
theorem leaf00169_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 31320763322353527373766747750400000000000 21675050635587713323445147521694180573184 127657844013661630578046900633600000000000 raw00169=true := by decide +kernel
#print axioms leaf00169_raw
theorem leaf00169_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00169=true := by decide +kernel
#print axioms leaf00169_rectangular
def affine00169 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00169 (IntegerComputedClassCell.leftNumerator ![(73/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(73/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(73/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00169_transform : affine00169=(NestedInteger.clearedAll 3 raw00169 (IntegerComputedClassCell.leftNumerator ![(73/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(73/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(73/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00169_transform
theorem leaf00169_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00169=true := by decide +kernel
#print axioms leaf00169_sign
theorem leaf00169_log : RationalLog.accepts (2540853739/4294967296) (-281827065/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00169_log
def leaf00169 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (16979019819/100000000000) (2540853739/4294967296) (-281827065/1073741824) 1 8 ![52,0,4] ![(73/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00169
theorem leaf00169_checked : FastNestedCellData.accepts 1 0 4 leaf00169=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (16979019819/100000000000) (2540853739/4294967296) (-281827065/1073741824) 1 8 ![52,0,4] ![(73/3200),0,(1/4)] ![(3/3200),1,(1/4)] 31320763322353527373766747750400000000000 21675050635587713323445147521694180573184 127657844013661630578046900633600000000000 raw00169 affine00169
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00169_raw leaf00169_rectangular
    leaf00169_transform leaf00169_sign leaf00169_log
#print axioms leaf00169_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
