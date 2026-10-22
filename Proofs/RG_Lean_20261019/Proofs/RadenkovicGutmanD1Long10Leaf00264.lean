/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00264 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 12526031440692000564473386500096000000000000 987200507304928880484249990731109224153088 1453823199623408678770623643648000000000000))
theorem leaf00264_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 12526031440692000564473386500096000000000000 987200507304928880484249990731109224153088 1453823199623408678770623643648000000000000 raw00264=true := by decide +kernel
#print axioms leaf00264_raw
theorem leaf00264_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00264=true := by decide +kernel
#print axioms leaf00264_rectangular
def affine00264 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00264 (IntegerComputedClassCell.leftNumerator ![(9/160),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/160),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/160),0,0] ![(1/640),1,(1/4)]))
theorem leaf00264_transform : affine00264=(NestedInteger.clearedAll 3 raw00264 (IntegerComputedClassCell.leftNumerator ![(9/160),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/160),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/160),0,0] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00264_transform
theorem leaf00264_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00264=true := by decide +kernel
#print axioms leaf00264_sign
theorem leaf00264_log : RationalLog.accepts (201600373/4294967296) (-821120415/536870912) 5 8=true := by decide +kernel
#print axioms leaf00264_log
def leaf00264 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (679037525031/1000000000000) (201600373/4294967296) (-821120415/536870912) 5 8 ![52,0,4] ![(9/160),0,0] ![(1/640),1,(1/4)] affine00264
theorem leaf00264_checked : FastNestedCellData.accepts 1 0 4 leaf00264=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (679037525031/1000000000000) (201600373/4294967296) (-821120415/536870912) 5 8 ![52,0,4] ![(9/160),0,0] ![(1/640),1,(1/4)] 12526031440692000564473386500096000000000000 987200507304928880484249990731109224153088 1453823199623408678770623643648000000000000 raw00264 affine00264
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00264_raw leaf00264_rectangular
    leaf00264_transform leaf00264_sign leaf00264_log
#print axioms leaf00264_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
