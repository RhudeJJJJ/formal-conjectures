/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00956 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 18002185748950758417276652748800000000000 6897474307688406406794236091254181986304 9816396208407547773949313024000000000000))
theorem leaf00956_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 18002185748950758417276652748800000000000 6897474307688406406794236091254181986304 9816396208407547773949313024000000000000 raw00956=true := by decide +kernel
#print axioms leaf00956_raw
theorem leaf00956_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00956=true := by decide +kernel
#print axioms leaf00956_rectangular
def affine00956 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00956 (IntegerComputedClassCell.leftNumerator ![(1/10),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/10),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/10),0,(1/16)] ![(1/320),1,(1/16)]))
theorem leaf00956_transform : affine00956=(NestedInteger.clearedAll 3 raw00956 (IntegerComputedClassCell.leftNumerator ![(1/10),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/10),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/10),0,(1/16)] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00956_transform
theorem leaf00956_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00956=true := by decide +kernel
#print axioms leaf00956_sign
theorem leaf00956_log : RationalLog.accepts (483247665/2147483648) (-3203020829/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00956_log
def leaf00956 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (351324160173/500000000000) (483247665/2147483648) (-3203020829/4294967296) 3 8 ![60,0,4] ![(1/10),0,(1/16)] ![(1/320),1,(1/16)] affine00956
theorem leaf00956_checked : FastNestedCellData.accepts 1 2 4 leaf00956=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (351324160173/500000000000) (483247665/2147483648) (-3203020829/4294967296) 3 8 ![60,0,4] ![(1/10),0,(1/16)] ![(1/320),1,(1/16)] 18002185748950758417276652748800000000000 6897474307688406406794236091254181986304 9816396208407547773949313024000000000000 raw00956 affine00956
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00956_raw leaf00956_rectangular
    leaf00956_transform leaf00956_sign leaf00956_log
#print axioms leaf00956_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
