/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00195 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6803060307609385656013551566848000000000000 2564212700726907961143261619744170573824 6952955479162390167167172608000000000000))
theorem leaf00195_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6803060307609385656013551566848000000000000 2564212700726907961143261619744170573824 6952955479162390167167172608000000000000 raw00195=true := by decide +kernel
#print axioms leaf00195_raw
theorem leaf00195_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00195=true := by decide +kernel
#print axioms leaf00195_rectangular
def affine00195 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00195 (IntegerComputedClassCell.leftNumerator ![(133/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(133/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(133/32000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00195_transform : affine00195=(NestedInteger.clearedAll 3 raw00195 (IntegerComputedClassCell.leftNumerator ![(133/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(133/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(133/32000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00195_transform
theorem leaf00195_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00195=true := by decide +kernel
#print axioms leaf00195_sign
theorem leaf00195_log : RationalLog.accepts (1182691/4294967296) (-17603797631/4294967296) 12 8=true := by decide +kernel
#print axioms leaf00195_log
def leaf00195 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (368794638253/1000000000000) (1182691/4294967296) (-17603797631/4294967296) 12 8 ![60,0,4] ![(133/32000),0,0] ![(3/32000),1,(1/16)] affine00195
theorem leaf00195_checked : FastNestedCellData.accepts 1 2 4 leaf00195=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (368794638253/1000000000000) (1182691/4294967296) (-17603797631/4294967296) 12 8 ![60,0,4] ![(133/32000),0,0] ![(3/32000),1,(1/16)] 6803060307609385656013551566848000000000000 2564212700726907961143261619744170573824 6952955479162390167167172608000000000000 raw00195 affine00195
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00195_raw leaf00195_rectangular
    leaf00195_transform leaf00195_sign leaf00195_log
#print axioms leaf00195_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
