/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00600 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 959771896692922773926930546688000000000000 13585470981750840201933566169945917620224 16319483513783461978201653248000000000000))
theorem leaf00600_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 959771896692922773926930546688000000000000 13585470981750840201933566169945917620224 16319483513783461978201653248000000000000 raw00600=true := by decide +kernel
#print axioms leaf00600_raw
theorem leaf00600_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00600=true := by decide +kernel
#print axioms leaf00600_rectangular
def affine00600 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00600 (IntegerComputedClassCell.leftNumerator ![(63/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(63/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(63/3200),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00600_transform : affine00600=(NestedInteger.clearedAll 3 raw00600 (IntegerComputedClassCell.leftNumerator ![(63/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(63/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(63/3200),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00600_transform
theorem leaf00600_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00600=true := by decide +kernel
#print axioms leaf00600_sign
theorem leaf00600_log : RationalLog.accepts (33176441/4294967296) (-5221992325/2147483648) 8 8=true := by decide +kernel
#print axioms leaf00600_log
def leaf00600 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (208117355097/250000000000) (33176441/4294967296) (-5221992325/2147483648) 8 8 ![60,0,4] ![(63/3200),0,0] ![(1/3200),1,(1/16)] affine00600
theorem leaf00600_checked : FastNestedCellData.accepts 1 2 4 leaf00600=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (208117355097/250000000000) (33176441/4294967296) (-5221992325/2147483648) 8 8 ![60,0,4] ![(63/3200),0,0] ![(1/3200),1,(1/16)] 959771896692922773926930546688000000000000 13585470981750840201933566169945917620224 16319483513783461978201653248000000000000 raw00600 affine00600
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00600_raw leaf00600_rectangular
    leaf00600_transform leaf00600_sign leaf00600_log
#print axioms leaf00600_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
