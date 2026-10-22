/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00085 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1280885636113745346942839291904000000000000 1091104374328537710255597562733803629182976 15713598922079076599412664827904000000000000))
theorem leaf00085_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1280885636113745346942839291904000000000000 1091104374328537710255597562733803629182976 15713598922079076599412664827904000000000000 raw00085=true := by decide +kernel
#print axioms leaf00085_raw
theorem leaf00085_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00085=true := by decide +kernel
#print axioms leaf00085_rectangular
def affine00085 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00085 (IntegerComputedClassCell.leftNumerator ![(29/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00085_transform : affine00085=(NestedInteger.clearedAll 3 raw00085 (IntegerComputedClassCell.leftNumerator ![(29/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00085_transform
theorem leaf00085_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00085=true := by decide +kernel
#print axioms leaf00085_sign
theorem leaf00085_log : RationalLog.accepts (3421059421/4294967296) (-488538963/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00085_log
def leaf00085 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (69436949469/1000000000000) (3421059421/4294967296) (-488538963/4294967296) 1 8 ![52,0,4] ![(29/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00085
theorem leaf00085_checked : FastNestedCellData.accepts 1 0 4 leaf00085=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (69436949469/1000000000000) (3421059421/4294967296) (-488538963/4294967296) 1 8 ![52,0,4] ![(29/3200),0,(1/4)] ![(1/3200),1,(1/4)] 1280885636113745346942839291904000000000000 1091104374328537710255597562733803629182976 15713598922079076599412664827904000000000000 raw00085 affine00085
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00085_raw leaf00085_rectangular
    leaf00085_transform leaf00085_sign leaf00085_log
#print axioms leaf00085_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
