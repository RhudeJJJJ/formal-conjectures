/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00323 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1339989240758437884857417728000000000000 874238631944918389684071999998017929216 2938248052522830722406285312000000000000))
theorem leaf00323_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1339989240758437884857417728000000000000 874238631944918389684071999998017929216 2938248052522830722406285312000000000000 raw00323=true := by decide +kernel
#print axioms leaf00323_raw
theorem leaf00323_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00323=true := by decide +kernel
#print axioms leaf00323_rectangular
def affine00323 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00323 (IntegerComputedClassCell.leftNumerator ![(33/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(33/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(33/320),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00323_transform : affine00323=(NestedInteger.clearedAll 3 raw00323 (IntegerComputedClassCell.leftNumerator ![(33/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(33/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(33/320),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00323_transform
theorem leaf00323_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00323=true := by decide +kernel
#print axioms leaf00323_sign
theorem leaf00323_log : RationalLog.accepts (2159576859/4294967296) (-184557873/536870912) 1 8=true := by decide +kernel
#print axioms leaf00323_log
def leaf00323 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (4649021587/15625000000) (2159576859/4294967296) (-184557873/536870912) 1 8 ![52,0,4] ![(33/320),0,(1/2)] ![(1/320),1,(1/2)] affine00323
theorem leaf00323_checked : FastNestedCellData.accepts 1 0 4 leaf00323=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (4649021587/15625000000) (2159576859/4294967296) (-184557873/536870912) 1 8 ![52,0,4] ![(33/320),0,(1/2)] ![(1/320),1,(1/2)] 1339989240758437884857417728000000000000 874238631944918389684071999998017929216 2938248052522830722406285312000000000000 raw00323 affine00323
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00323_raw leaf00323_rectangular
    leaf00323_transform leaf00323_sign leaf00323_log
#print axioms leaf00323_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
