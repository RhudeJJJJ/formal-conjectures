/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00136 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 111162429668172761695095095296000000000000 89149763053839436580966702830867158401024 924617060477983307721756114944000000000000))
theorem leaf00136_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 111162429668172761695095095296000000000000 89149763053839436580966702830867158401024 924617060477983307721756114944000000000000 raw00136=true := by decide +kernel
#print axioms leaf00136_raw
theorem leaf00136_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00136=true := by decide +kernel
#print axioms leaf00136_rectangular
def affine00136 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00136 (IntegerComputedClassCell.leftNumerator ![(97/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(97/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(97/32000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00136_transform : affine00136=(NestedInteger.clearedAll 3 raw00136 (IntegerComputedClassCell.leftNumerator ![(97/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(97/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(97/32000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00136_transform
theorem leaf00136_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00136=true := by decide +kernel
#print axioms leaf00136_sign
theorem leaf00136_log : RationalLog.accepts (3141563569/4294967296) (-671568237/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00136_log
def leaf00136 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (24104509549/250000000000) (3141563569/4294967296) (-671568237/4294967296) 1 8 ![60,0,4] ![(97/32000),0,(1/16)] ![(3/32000),1,(1/16)] affine00136
theorem leaf00136_checked : FastNestedCellData.accepts 1 2 4 leaf00136=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (24104509549/250000000000) (3141563569/4294967296) (-671568237/4294967296) 1 8 ![60,0,4] ![(97/32000),0,(1/16)] ![(3/32000),1,(1/16)] 111162429668172761695095095296000000000000 89149763053839436580966702830867158401024 924617060477983307721756114944000000000000 raw00136 affine00136
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00136_raw leaf00136_rectangular
    leaf00136_transform leaf00136_sign leaf00136_log
#print axioms leaf00136_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
