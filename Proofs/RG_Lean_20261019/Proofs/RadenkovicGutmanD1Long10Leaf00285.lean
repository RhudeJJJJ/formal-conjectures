/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00285 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2013700183617451406555663564800000000000 226396613193637523355341144053438742528 324052118141298721694312038400000000000))
theorem leaf00285_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2013700183617451406555663564800000000000 226396613193637523355341144053438742528 324052118141298721694312038400000000000 raw00285=true := by decide +kernel
#print axioms leaf00285_raw
theorem leaf00285_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00285=true := by decide +kernel
#print axioms leaf00285_rectangular
def affine00285 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00285 (IntegerComputedClassCell.leftNumerator ![(43/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(43/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(43/640),0,0] ![(1/640),1,(1/4)]))
theorem leaf00285_transform : affine00285=(NestedInteger.clearedAll 3 raw00285 (IntegerComputedClassCell.leftNumerator ![(43/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(43/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(43/640),0,0] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00285_transform
theorem leaf00285_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00285=true := by decide +kernel
#print axioms leaf00285_sign
theorem leaf00285_log : RationalLog.accepts (71067817/1073741824) (-5830998643/4294967296) 4 8=true := by decide +kernel
#print axioms leaf00285_log
def leaf00285 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (34932129821/50000000000) (71067817/1073741824) (-5830998643/4294967296) 4 8 ![52,0,4] ![(43/640),0,0] ![(1/640),1,(1/4)] affine00285
theorem leaf00285_checked : FastNestedCellData.accepts 1 0 4 leaf00285=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (34932129821/50000000000) (71067817/1073741824) (-5830998643/4294967296) 4 8 ![52,0,4] ![(43/640),0,0] ![(1/640),1,(1/4)] 2013700183617451406555663564800000000000 226396613193637523355341144053438742528 324052118141298721694312038400000000000 raw00285 affine00285
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00285_raw leaf00285_rectangular
    leaf00285_transform leaf00285_sign leaf00285_log
#print axioms leaf00285_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
