/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00320 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1347776399912661844207964520448000000000000 878541777962849588016589063334031217655808 3006106082802874318722573533184000000000000))
theorem leaf00320_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1347776399912661844207964520448000000000000 878541777962849588016589063334031217655808 3006106082802874318722573533184000000000000 raw00320=true := by decide +kernel
#print axioms leaf00320_raw
theorem leaf00320_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00320=true := by decide +kernel
#print axioms leaf00320_rectangular
def affine00320 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00320 (IntegerComputedClassCell.leftNumerator ![(1/10),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/10),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/10),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00320_transform : affine00320=(NestedInteger.clearedAll 3 raw00320 (IntegerComputedClassCell.leftNumerator ![(1/10),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/10),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/10),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00320_transform
theorem leaf00320_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00320=true := by decide +kernel
#print axioms leaf00320_sign
theorem leaf00320_log : RationalLog.accepts (2166491943/4294967296) (-1469597609/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00320_log
def leaf00320 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (146126210081/500000000000) (2166491943/4294967296) (-1469597609/4294967296) 1 8 ![52,0,4] ![(1/10),0,(1/2)] ![(1/320),1,(1/2)] affine00320
theorem leaf00320_checked : FastNestedCellData.accepts 1 0 4 leaf00320=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (146126210081/500000000000) (2166491943/4294967296) (-1469597609/4294967296) 1 8 ![52,0,4] ![(1/10),0,(1/2)] ![(1/320),1,(1/2)] 1347776399912661844207964520448000000000000 878541777962849588016589063334031217655808 3006106082802874318722573533184000000000000 raw00320 affine00320
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00320_raw leaf00320_rectangular
    leaf00320_transform leaf00320_sign leaf00320_log
#print axioms leaf00320_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
