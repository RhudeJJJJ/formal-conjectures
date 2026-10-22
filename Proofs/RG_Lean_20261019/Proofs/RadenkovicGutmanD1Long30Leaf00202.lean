/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00202 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 61435975810028686547084745113600000000000 52758300467694184883266456340098170486784 792059419305715054230951165952000000000000))
theorem leaf00202_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 61435975810028686547084745113600000000000 52758300467694184883266456340098170486784 792059419305715054230951165952000000000000 raw00202=true := by decide +kernel
#print axioms leaf00202_raw
theorem leaf00202_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00202=true := by decide +kernel
#print axioms leaf00202_rectangular
def affine00202 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00202 (IntegerComputedClassCell.leftNumerator ![(17/4000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/4000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/4000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00202_transform : affine00202=(NestedInteger.clearedAll 3 raw00202 (IntegerComputedClassCell.leftNumerator ![(17/4000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/4000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/4000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00202_transform
theorem leaf00202_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00202=true := by decide +kernel
#print axioms leaf00202_sign
theorem leaf00202_log : RationalLog.accepts (3457981345/4294967296) (-465486333/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00202_log
def leaf00202 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (33304509221/500000000000) (3457981345/4294967296) (-465486333/4294967296) 1 8 ![60,0,4] ![(17/4000),0,(1/8)] ![(3/32000),1,(1/8)] affine00202
theorem leaf00202_checked : FastNestedCellData.accepts 1 2 4 leaf00202=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (33304509221/500000000000) (3457981345/4294967296) (-465486333/4294967296) 1 8 ![60,0,4] ![(17/4000),0,(1/8)] ![(3/32000),1,(1/8)] 61435975810028686547084745113600000000000 52758300467694184883266456340098170486784 792059419305715054230951165952000000000000 raw00202 affine00202
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00202_raw leaf00202_rectangular
    leaf00202_transform leaf00202_sign leaf00202_log
#print axioms leaf00202_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
