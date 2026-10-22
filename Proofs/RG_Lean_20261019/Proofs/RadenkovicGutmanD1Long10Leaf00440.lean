/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00440 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 24149089782975928066228879360000000000 26858957244016253789781112121515311104 3205738774859754994103484416000000000000))
theorem leaf00440_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 24149089782975928066228879360000000000 26858957244016253789781112121515311104 3205738774859754994103484416000000000000 raw00440=true := by decide +kernel
#print axioms leaf00440_raw
theorem leaf00440_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00440=true := by decide +kernel
#print axioms leaf00440_rectangular
def affine00440 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00440 (IntegerComputedClassCell.leftNumerator ![(17/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/64),0,(3/4)] ![(1/64),1,(1/4)]))
theorem leaf00440_transform : affine00440=(NestedInteger.clearedAll 3 raw00440 (IntegerComputedClassCell.leftNumerator ![(17/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/64),0,(3/4)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00440_transform
theorem leaf00440_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00440=true := by decide +kernel
#print axioms leaf00440_sign
theorem leaf00440_log : RationalLog.accepts (592154075/536870912) (210473121/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00440_log
def leaf00440 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (4189199297/500000000000) (592154075/536870912) (210473121/4294967296) 0 8 ![52,0,4] ![(17/64),0,(3/4)] ![(1/64),1,(1/4)] affine00440
theorem leaf00440_checked : FastNestedCellData.accepts 1 0 4 leaf00440=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (4189199297/500000000000) (592154075/536870912) (210473121/4294967296) 0 8 ![52,0,4] ![(17/64),0,(3/4)] ![(1/64),1,(1/4)] 24149089782975928066228879360000000000 26858957244016253789781112121515311104 3205738774859754994103484416000000000000 raw00440 affine00440
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00440_raw leaf00440_rectangular
    leaf00440_transform leaf00440_sign leaf00440_log
#print axioms leaf00440_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
