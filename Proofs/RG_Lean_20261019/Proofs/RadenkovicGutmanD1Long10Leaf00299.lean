/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00299 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 4587433623987224990395356151808000000000000 3022177335172668593620634512658278511542272 12152618744342839006961854316544000000000000))
theorem leaf00299_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 4587433623987224990395356151808000000000000 3022177335172668593620634512658278511542272 12152618744342839006961854316544000000000000 raw00299=true := by decide +kernel
#print axioms leaf00299_raw
theorem leaf00299_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00299=true := by decide +kernel
#print axioms leaf00299_rectangular
def affine00299 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00299 (IntegerComputedClassCell.leftNumerator ![(5/64),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/64),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00299_transform : affine00299=(NestedInteger.clearedAll 3 raw00299 (IntegerComputedClassCell.leftNumerator ![(5/64),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/64),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00299_transform
theorem leaf00299_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00299=true := by decide +kernel
#print axioms leaf00299_sign
theorem leaf00299_log : RationalLog.accepts (2265984953/4294967296) (-686587497/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00299_log
def leaf00299 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (248685275063/1000000000000) (2265984953/4294967296) (-686587497/2147483648) 1 8 ![52,0,4] ![(5/64),0,(1/2)] ![(1/320),1,(1/2)] affine00299
theorem leaf00299_checked : FastNestedCellData.accepts 1 0 4 leaf00299=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (248685275063/1000000000000) (2265984953/4294967296) (-686587497/2147483648) 1 8 ![52,0,4] ![(5/64),0,(1/2)] ![(1/320),1,(1/2)] 4587433623987224990395356151808000000000000 3022177335172668593620634512658278511542272 12152618744342839006961854316544000000000000 raw00299 affine00299
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00299_raw leaf00299_rectangular
    leaf00299_transform leaf00299_sign leaf00299_log
#print axioms leaf00299_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
