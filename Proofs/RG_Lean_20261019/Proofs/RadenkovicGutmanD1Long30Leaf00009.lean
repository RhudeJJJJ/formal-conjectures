/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00009 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 290990727911696815290843136000000000000 288107505762738039075928632649920282624 71343626095987602672869965824000000000000))
theorem leaf00009_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 290990727911696815290843136000000000000 288107505762738039075928632649920282624 71343626095987602672869965824000000000000 raw00009=true := by decide +kernel
#print axioms leaf00009_raw
theorem leaf00009_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00009=true := by decide +kernel
#print axioms leaf00009_rectangular
def affine00009 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00009 (IntegerComputedClassCell.leftNumerator ![(17/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/16000),0,(1/2)] ![(1/16000),1,(1/2)]))
theorem leaf00009_transform : affine00009=(NestedInteger.clearedAll 3 raw00009 (IntegerComputedClassCell.leftNumerator ![(17/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/16000),0,(1/2)] ![(1/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00009_transform
theorem leaf00009_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00009=true := by decide +kernel
#print axioms leaf00009_sign
theorem leaf00009_log : RationalLog.accepts (2117654007/2147483648) (-30038791/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00009_log
def leaf00009 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (504788447/125000000000) (2117654007/2147483648) (-30038791/4294967296) 1 8 ![60,0,4] ![(17/16000),0,(1/2)] ![(1/16000),1,(1/2)] affine00009
theorem leaf00009_checked : FastNestedCellData.accepts 1 2 4 leaf00009=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (504788447/125000000000) (2117654007/2147483648) (-30038791/4294967296) 1 8 ![60,0,4] ![(17/16000),0,(1/2)] ![(1/16000),1,(1/2)] 290990727911696815290843136000000000000 288107505762738039075928632649920282624 71343626095987602672869965824000000000000 raw00009 affine00009
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00009_raw leaf00009_rectangular
    leaf00009_transform leaf00009_sign leaf00009_log
#print axioms leaf00009_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
