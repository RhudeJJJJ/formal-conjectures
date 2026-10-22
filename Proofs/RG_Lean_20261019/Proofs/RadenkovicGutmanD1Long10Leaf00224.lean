/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00224 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 25825237717252730774807275110400000000000 19361074871762462930263903356538939506688 138294484279900889196187038515200000000000))
theorem leaf00224_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 25825237717252730774807275110400000000000 19361074871762462930263903356538939506688 138294484279900889196187038515200000000000 raw00224=true := by decide +kernel
#print axioms leaf00224_raw
theorem leaf00224_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00224=true := by decide +kernel
#print axioms leaf00224_rectangular
def affine00224 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00224 (IntegerComputedClassCell.leftNumerator ![(127/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(127/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(127/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00224_transform : affine00224=(NestedInteger.clearedAll 3 raw00224 (IntegerComputedClassCell.leftNumerator ![(127/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(127/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(127/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00224_transform
theorem leaf00224_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00224=true := by decide +kernel
#print axioms leaf00224_sign
theorem leaf00224_log : RationalLog.accepts (2824493423/4294967296) (-900042455/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00224_log
def leaf00224 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (13999889419/100000000000) (2824493423/4294967296) (-900042455/4294967296) 1 8 ![52,0,4] ![(127/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00224
theorem leaf00224_checked : FastNestedCellData.accepts 1 0 4 leaf00224=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (13999889419/100000000000) (2824493423/4294967296) (-900042455/4294967296) 1 8 ![52,0,4] ![(127/3200),0,(1/2)] ![(3/3200),1,(1/2)] 25825237717252730774807275110400000000000 19361074871762462930263903356538939506688 138294484279900889196187038515200000000000 raw00224 affine00224
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00224_raw leaf00224_rectangular
    leaf00224_transform leaf00224_sign leaf00224_log
#print axioms leaf00224_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
