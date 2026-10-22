/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00876 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 209933758410074675117012549632000000000000 56662897260777732918167979244406538502144 77795816713849654949548392448000000000000))
theorem leaf00876_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 209933758410074675117012549632000000000000 56662897260777732918167979244406538502144 77795816713849654949548392448000000000000 raw00876=true := by decide +kernel
#print axioms leaf00876_raw
theorem leaf00876_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00876=true := by decide +kernel
#print axioms leaf00876_rectangular
def affine00876 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00876 (IntegerComputedClassCell.leftNumerator ![(39/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(39/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(39/640),0,(1/16)] ![(1/640),1,(1/16)]))
theorem leaf00876_transform : affine00876=(NestedInteger.clearedAll 3 raw00876 (IntegerComputedClassCell.leftNumerator ![(39/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(39/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(39/640),0,(1/16)] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00876_transform
theorem leaf00876_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00876=true := by decide +kernel
#print axioms leaf00876_sign
theorem leaf00876_log : RationalLog.accepts (335361847/2147483648) (-3987537831/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00876_log
def leaf00876 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (182088509557/250000000000) (335361847/2147483648) (-3987537831/4294967296) 3 8 ![60,0,4] ![(39/640),0,(1/16)] ![(1/640),1,(1/16)] affine00876
theorem leaf00876_checked : FastNestedCellData.accepts 1 2 4 leaf00876=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (182088509557/250000000000) (335361847/2147483648) (-3987537831/4294967296) 3 8 ![60,0,4] ![(39/640),0,(1/16)] ![(1/640),1,(1/16)] 209933758410074675117012549632000000000000 56662897260777732918167979244406538502144 77795816713849654949548392448000000000000 raw00876 affine00876
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00876_raw leaf00876_rectangular
    leaf00876_transform leaf00876_sign leaf00876_log
#print axioms leaf00876_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
