/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00941 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3294206479864576537197405011968000000000000 1157796529876510221027298688173233886199808 1620843775777755728865524711424000000000000))
theorem leaf00941_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3294206479864576537197405011968000000000000 1157796529876510221027298688173233886199808 1620843775777755728865524711424000000000000 raw00941=true := by decide +kernel
#print axioms leaf00941_raw
theorem leaf00941_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00941=true := by decide +kernel
#print axioms leaf00941_rectangular
def affine00941 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00941 (IntegerComputedClassCell.leftNumerator ![(29/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/320),0,(1/16)] ![(1/320),1,(1/16)]))
theorem leaf00941_transform : affine00941=(NestedInteger.clearedAll 3 raw00941 (IntegerComputedClassCell.leftNumerator ![(29/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/320),0,(1/16)] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00941_transform
theorem leaf00941_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00941=true := by decide +kernel
#print axioms leaf00941_sign
theorem leaf00941_log : RationalLog.accepts (440271039/2147483648) (-3403034775/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00941_log
def leaf00941 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (714317164417/1000000000000) (440271039/2147483648) (-3403034775/4294967296) 3 8 ![60,0,4] ![(29/320),0,(1/16)] ![(1/320),1,(1/16)] affine00941
theorem leaf00941_checked : FastNestedCellData.accepts 1 2 4 leaf00941=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (714317164417/1000000000000) (440271039/2147483648) (-3403034775/4294967296) 3 8 ![60,0,4] ![(29/320),0,(1/16)] ![(1/320),1,(1/16)] 3294206479864576537197405011968000000000000 1157796529876510221027298688173233886199808 1620843775777755728865524711424000000000000 raw00941 affine00941
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00941_raw leaf00941_rectangular
    leaf00941_transform leaf00941_sign leaf00941_log
#print axioms leaf00941_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
