/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00101 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 180234890529711244191251562496000000000000 164425688668079526331638921881450899832832 4207174577975936094891795283968000000000000))
theorem leaf00101_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 180234890529711244191251562496000000000000 164425688668079526331638921881450899832832 4207174577975936094891795283968000000000000 raw00101=true := by decide +kernel
#print axioms leaf00101_raw
theorem leaf00101_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00101=true := by decide +kernel
#print axioms leaf00101_rectangular
def affine00101 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00101 (IntegerComputedClassCell.leftNumerator ![(17/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/1600),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00101_transform : affine00101=(NestedInteger.clearedAll 3 raw00101 (IntegerComputedClassCell.leftNumerator ![(17/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/1600),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00101_transform
theorem leaf00101_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00101=true := by decide +kernel
#print axioms leaf00101_sign
theorem leaf00101_log : RationalLog.accepts (3770862993/4294967296) (-69868419/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00101_log
def leaf00101 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (19541105987/500000000000) (3770862993/4294967296) (-69868419/1073741824) 1 8 ![52,0,4] ![(17/1600),0,(1/2)] ![(1/3200),1,(1/2)] affine00101
theorem leaf00101_checked : FastNestedCellData.accepts 1 0 4 leaf00101=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (19541105987/500000000000) (3770862993/4294967296) (-69868419/1073741824) 1 8 ![52,0,4] ![(17/1600),0,(1/2)] ![(1/3200),1,(1/2)] 180234890529711244191251562496000000000000 164425688668079526331638921881450899832832 4207174577975936094891795283968000000000000 raw00101 affine00101
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00101_raw leaf00101_rectangular
    leaf00101_transform leaf00101_sign leaf00101_log
#print axioms leaf00101_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
