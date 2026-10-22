/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00177 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 144305938994133307053307854848000000000 1978568659788782668154432349643210752 4046752332306433213772857344000000000))
theorem leaf00177_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 144305938994133307053307854848000000000 1978568659788782668154432349643210752 4046752332306433213772857344000000000 raw00177=true := by decide +kernel
#print axioms leaf00177_raw
theorem leaf00177_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00177=true := by decide +kernel
#print axioms leaf00177_rectangular
def affine00177 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00177 (IntegerComputedClassCell.leftNumerator ![(41/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/1600),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00177_transform : affine00177=(NestedInteger.clearedAll 3 raw00177 (IntegerComputedClassCell.leftNumerator ![(41/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/1600),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00177_transform
theorem leaf00177_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00177=true := by decide +kernel
#print axioms leaf00177_sign
theorem leaf00177_log : RationalLog.accepts (39550613/4294967296) (-10066583307/4294967296) 7 8=true := by decide +kernel
#print axioms leaf00177_log
def leaf00177 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (1955710157/4000000000) (39550613/4294967296) (-10066583307/4294967296) 7 8 ![52,0,4] ![(41/1600),0,0] ![(3/3200),1,(1/4)] affine00177
theorem leaf00177_checked : FastNestedCellData.accepts 1 0 4 leaf00177=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (1955710157/4000000000) (39550613/4294967296) (-10066583307/4294967296) 7 8 ![52,0,4] ![(41/1600),0,0] ![(3/3200),1,(1/4)] 144305938994133307053307854848000000000 1978568659788782668154432349643210752 4046752332306433213772857344000000000 raw00177 affine00177
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00177_raw leaf00177_rectangular
    leaf00177_transform leaf00177_sign leaf00177_log
#print axioms leaf00177_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
