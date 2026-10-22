/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00174 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12711961786983291698742611148800000000000 12303506515560718712943258450655275122688 892701062609262756612179755008000000000000))
theorem leaf00174_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12711961786983291698742611148800000000000 12303506515560718712943258450655275122688 892701062609262756612179755008000000000000 raw00174=true := by decide +kernel
#print axioms leaf00174_raw
theorem leaf00174_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00174=true := by decide +kernel
#print axioms leaf00174_rectangular
def affine00174 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00174 (IntegerComputedClassCell.leftNumerator ![(59/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(59/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(59/16000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00174_transform : affine00174=(NestedInteger.clearedAll 3 raw00174 (IntegerComputedClassCell.leftNumerator ![(59/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(59/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(59/16000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00174_transform
theorem leaf00174_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00174=true := by decide +kernel
#print axioms leaf00174_sign
theorem leaf00174_log : RationalLog.accepts (4100449485/4294967296) (-99530197/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00174_log
def leaf00174 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (6891168293/500000000000) (4100449485/4294967296) (-99530197/4294967296) 1 8 ![60,0,4] ![(59/16000),0,(1/2)] ![(3/32000),1,(1/2)] affine00174
theorem leaf00174_checked : FastNestedCellData.accepts 1 2 4 leaf00174=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (6891168293/500000000000) (4100449485/4294967296) (-99530197/4294967296) 1 8 ![60,0,4] ![(59/16000),0,(1/2)] ![(3/32000),1,(1/2)] 12711961786983291698742611148800000000000 12303506515560718712943258450655275122688 892701062609262756612179755008000000000000 raw00174 affine00174
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00174_raw leaf00174_rectangular
    leaf00174_transform leaf00174_sign leaf00174_log
#print axioms leaf00174_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
