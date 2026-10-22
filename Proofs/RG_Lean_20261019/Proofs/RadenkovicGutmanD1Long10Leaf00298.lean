/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00298 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 7870830044711141857013050376192000000000000 4015557716919542908534643480663960032641024 9411201245159491631230539005952000000000000))
theorem leaf00298_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 7870830044711141857013050376192000000000000 4015557716919542908534643480663960032641024 9411201245159491631230539005952000000000000 raw00298=true := by decide +kernel
#print axioms leaf00298_raw
theorem leaf00298_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00298=true := by decide +kernel
#print axioms leaf00298_rectangular
def affine00298 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00298 (IntegerComputedClassCell.leftNumerator ![(5/64),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/64),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00298_transform : affine00298=(NestedInteger.clearedAll 3 raw00298 (IntegerComputedClassCell.leftNumerator ![(5/64),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/64),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00298_transform
theorem leaf00298_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00298=true := by decide +kernel
#print axioms leaf00298_sign
theorem leaf00298_log : RationalLog.accepts (1535886301/4294967296) (-276041941/536870912) 2 8=true := by decide +kernel
#print axioms leaf00298_log
def leaf00298 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (426678551687/1000000000000) (1535886301/4294967296) (-276041941/536870912) 2 8 ![52,0,4] ![(5/64),0,(1/4)] ![(1/320),1,(1/4)] affine00298
theorem leaf00298_checked : FastNestedCellData.accepts 1 0 4 leaf00298=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (426678551687/1000000000000) (1535886301/4294967296) (-276041941/536870912) 2 8 ![52,0,4] ![(5/64),0,(1/4)] ![(1/320),1,(1/4)] 7870830044711141857013050376192000000000000 4015557716919542908534643480663960032641024 9411201245159491631230539005952000000000000 raw00298 affine00298
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00298_raw leaf00298_rectangular
    leaf00298_transform leaf00298_sign leaf00298_log
#print axioms leaf00298_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
