/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00937 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11035823046720532651631272001536000000000000 4622164080449917404285772794697678558593024 7726100490899966662085122719744000000000000))
theorem leaf00937_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11035823046720532651631272001536000000000000 4622164080449917404285772794697678558593024 7726100490899966662085122719744000000000000 raw00937=true := by decide +kernel
#print axioms leaf00937_raw
theorem leaf00937_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00937=true := by decide +kernel
#print axioms leaf00937_rectangular
def affine00937 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00937 (IntegerComputedClassCell.leftNumerator ![(7/80),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/80),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/80),0,(1/8)] ![(1/320),1,(1/8)]))
theorem leaf00937_transform : affine00937=(NestedInteger.clearedAll 3 raw00937 (IntegerComputedClassCell.leftNumerator ![(7/80),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/80),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/80),0,(1/8)] ![(1/320),1,(1/8)])) := by decide +kernel
#print axioms leaf00937_transform
theorem leaf00937_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00937=true := by decide +kernel
#print axioms leaf00937_sign
theorem leaf00937_log : RationalLog.accepts (1125524409/4294967296) (-2875899161/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00937_log
def leaf00937 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (598253166121/1000000000000) (1125524409/4294967296) (-2875899161/4294967296) 2 8 ![60,0,4] ![(7/80),0,(1/8)] ![(1/320),1,(1/8)] affine00937
theorem leaf00937_checked : FastNestedCellData.accepts 1 2 4 leaf00937=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (598253166121/1000000000000) (1125524409/4294967296) (-2875899161/4294967296) 2 8 ![60,0,4] ![(7/80),0,(1/8)] ![(1/320),1,(1/8)] 11035823046720532651631272001536000000000000 4622164080449917404285772794697678558593024 7726100490899966662085122719744000000000000 raw00937 affine00937
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00937_raw leaf00937_rectangular
    leaf00937_transform leaf00937_sign leaf00937_log
#print axioms leaf00937_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
