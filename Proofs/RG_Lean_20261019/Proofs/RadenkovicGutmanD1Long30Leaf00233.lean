/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00233 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 170411811522606237592496111616000000000000 156459375958582586657590146665605773656064 4234105078240731695695072854016000000000000))
theorem leaf00233_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 170411811522606237592496111616000000000000 156459375958582586657590146665605773656064 4234105078240731695695072854016000000000000 raw00233=true := by decide +kernel
#print axioms leaf00233_raw
theorem leaf00233_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00233=true := by decide +kernel
#print axioms leaf00233_rectangular
def affine00233 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00233 (IntegerComputedClassCell.leftNumerator ![(77/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(77/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(77/16000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00233_transform : affine00233=(NestedInteger.clearedAll 3 raw00233 (IntegerComputedClassCell.leftNumerator ![(77/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(77/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(77/16000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00233_transform
theorem leaf00233_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00233=true := by decide +kernel
#print axioms leaf00233_sign
theorem leaf00233_log : RationalLog.accepts (3802796071/4294967296) (-261364551/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00233_log
def leaf00233 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (18476085627/500000000000) (3802796071/4294967296) (-261364551/4294967296) 1 8 ![60,0,4] ![(77/16000),0,(1/4)] ![(3/32000),1,(1/4)] affine00233
theorem leaf00233_checked : FastNestedCellData.accepts 1 2 4 leaf00233=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (18476085627/500000000000) (3802796071/4294967296) (-261364551/4294967296) 1 8 ![60,0,4] ![(77/16000),0,(1/4)] ![(3/32000),1,(1/4)] 170411811522606237592496111616000000000000 156459375958582586657590146665605773656064 4234105078240731695695072854016000000000000 raw00233 affine00233
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00233_raw leaf00233_rectangular
    leaf00233_transform leaf00233_sign leaf00233_log
#print axioms leaf00233_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
