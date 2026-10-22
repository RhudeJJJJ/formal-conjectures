/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00282 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 196086633103291829071118336000000000000 21050945811067837065268394517369716736 30217839880938467471917056000000000000))
theorem leaf00282_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 196086633103291829071118336000000000000 21050945811067837065268394517369716736 30217839880938467471917056000000000000 raw00282=true := by decide +kernel
#print axioms leaf00282_raw
theorem leaf00282_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00282=true := by decide +kernel
#print axioms leaf00282_rectangular
def affine00282 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00282 (IntegerComputedClassCell.leftNumerator ![(21/320),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/320),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/320),0,0] ![(1/640),1,(1/4)]))
theorem leaf00282_transform : affine00282=(NestedInteger.clearedAll 3 raw00282 (IntegerComputedClassCell.leftNumerator ![(21/320),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/320),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/320),0,0] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00282_transform
theorem leaf00282_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00282=true := by decide +kernel
#print axioms leaf00282_sign
theorem leaf00282_log : RationalLog.accepts (8492663/134217728) (-5927614865/4294967296) 4 8=true := by decide +kernel
#print axioms leaf00282_log
def leaf00282 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (87079957957/125000000000) (8492663/134217728) (-5927614865/4294967296) 4 8 ![52,0,4] ![(21/320),0,0] ![(1/640),1,(1/4)] affine00282
theorem leaf00282_checked : FastNestedCellData.accepts 1 0 4 leaf00282=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (87079957957/125000000000) (8492663/134217728) (-5927614865/4294967296) 4 8 ![52,0,4] ![(21/320),0,0] ![(1/640),1,(1/4)] 196086633103291829071118336000000000000 21050945811067837065268394517369716736 30217839880938467471917056000000000000 raw00282 affine00282
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00282_raw leaf00282_rectangular
    leaf00282_transform leaf00282_sign leaf00282_log
#print axioms leaf00282_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
