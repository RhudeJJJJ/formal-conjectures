/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00119 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2242537467598098591572715110400000000000 1999160224127102193862543682139718680576 41111907325578801370426349977600000000000))
theorem leaf00119_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2242537467598098591572715110400000000000 1999160224127102193862543682139718680576 41111907325578801370426349977600000000000 raw00119=true := by decide +kernel
#print axioms leaf00119_raw
theorem leaf00119_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00119=true := by decide +kernel
#print axioms leaf00119_rectangular
def affine00119 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00119 (IntegerComputedClassCell.leftNumerator ![(21/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/1600),0,(1/2)] ![(1/1600),1,(1/2)]))
theorem leaf00119_transform : affine00119=(NestedInteger.clearedAll 3 raw00119 (IntegerComputedClassCell.leftNumerator ![(21/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/1600),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/1600),0,(1/2)] ![(1/1600),1,(1/2)])) := by decide +kernel
#print axioms leaf00119_transform
theorem leaf00119_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00119=true := by decide +kernel
#print axioms leaf00119_sign
theorem leaf00119_log : RationalLog.accepts (912823081/1073741824) (-348671439/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00119_log
def leaf00119 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (9725455977/200000000000) (912823081/1073741824) (-348671439/4294967296) 1 8 ![52,0,4] ![(21/1600),0,(1/2)] ![(1/1600),1,(1/2)] affine00119
theorem leaf00119_checked : FastNestedCellData.accepts 1 0 4 leaf00119=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (9725455977/200000000000) (912823081/1073741824) (-348671439/4294967296) 1 8 ![52,0,4] ![(21/1600),0,(1/2)] ![(1/1600),1,(1/2)] 2242537467598098591572715110400000000000 1999160224127102193862543682139718680576 41111907325578801370426349977600000000000 raw00119 affine00119
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00119_raw leaf00119_rectangular
    leaf00119_transform leaf00119_sign leaf00119_log
#print axioms leaf00119_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
