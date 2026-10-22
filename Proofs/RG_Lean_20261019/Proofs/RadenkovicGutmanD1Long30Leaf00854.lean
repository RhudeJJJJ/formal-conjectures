/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00854 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 33651272587251520419289418956800000000000 23763513386206302085290777690189317799936 130265340958780621628210623283200000000000))
theorem leaf00854_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 33651272587251520419289418956800000000000 23763513386206302085290777690189317799936 130265340958780621628210623283200000000000 raw00854=true := by decide +kernel
#print axioms leaf00854_raw
theorem leaf00854_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00854=true := by decide +kernel
#print axioms leaf00854_rectangular
def affine00854 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00854 (IntegerComputedClassCell.leftNumerator ![(17/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/320),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00854_transform : affine00854=(NestedInteger.clearedAll 3 raw00854 (IntegerComputedClassCell.leftNumerator ![(17/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/320),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00854_transform
theorem leaf00854_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00854=true := by decide +kernel
#print axioms leaf00854_sign
theorem leaf00854_log : RationalLog.accepts (2565049879/4294967296) (-1106954877/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00854_log
def leaf00854 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (18242391423/100000000000) (2565049879/4294967296) (-1106954877/4294967296) 1 8 ![60,0,4] ![(17/320),0,(1/2)] ![(1/640),1,(1/2)] affine00854
theorem leaf00854_checked : FastNestedCellData.accepts 1 2 4 leaf00854=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (18242391423/100000000000) (2565049879/4294967296) (-1106954877/4294967296) 1 8 ![60,0,4] ![(17/320),0,(1/2)] ![(1/640),1,(1/2)] 33651272587251520419289418956800000000000 23763513386206302085290777690189317799936 130265340958780621628210623283200000000000 raw00854 affine00854
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00854_raw leaf00854_rectangular
    leaf00854_transform leaf00854_sign leaf00854_log
#print axioms leaf00854_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
