/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00319 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 345344089928952764615218744524800000000000 181148874092765275155328046469624178409472 387046660658630694750681405849600000000000))
theorem leaf00319_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 345344089928952764615218744524800000000000 181148874092765275155328046469624178409472 387046660658630694750681405849600000000000 raw00319=true := by decide +kernel
#print axioms leaf00319_raw
theorem leaf00319_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00319=true := by decide +kernel
#print axioms leaf00319_rectangular
def affine00319 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00319 (IntegerComputedClassCell.leftNumerator ![(1/10),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/10),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/10),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00319_transform : affine00319=(NestedInteger.clearedAll 3 raw00319 (IntegerComputedClassCell.leftNumerator ![(1/10),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/10),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/10),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00319_transform
theorem leaf00319_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00319=true := by decide +kernel
#print axioms leaf00319_sign
theorem leaf00319_log : RationalLog.accepts (1534648717/4294967296) (-1105033311/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00319_log
def leaf00319 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (93605703139/200000000000) (1534648717/4294967296) (-1105033311/2147483648) 2 8 ![52,0,4] ![(1/10),0,(1/4)] ![(1/320),1,(1/4)] affine00319
theorem leaf00319_checked : FastNestedCellData.accepts 1 0 4 leaf00319=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (93605703139/200000000000) (1534648717/4294967296) (-1105033311/2147483648) 2 8 ![52,0,4] ![(1/10),0,(1/4)] ![(1/320),1,(1/4)] 345344089928952764615218744524800000000000 181148874092765275155328046469624178409472 387046660658630694750681405849600000000000 raw00319 affine00319
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00319_raw leaf00319_rectangular
    leaf00319_transform leaf00319_sign leaf00319_log
#print axioms leaf00319_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
