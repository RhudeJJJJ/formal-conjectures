/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00511 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7275953046594240298430670831616000000000000 3085997444596598951286516021600794393444352 7823937937483198106871741284352000000000000))
theorem leaf00511_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7275953046594240298430670831616000000000000 3085997444596598951286516021600794393444352 7823937937483198106871741284352000000000000 raw00511=true := by decide +kernel
#print axioms leaf00511_raw
theorem leaf00511_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00511=true := by decide +kernel
#print axioms leaf00511_rectangular
def affine00511 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00511 (IntegerComputedClassCell.leftNumerator ![(9/640),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/640),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/640),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00511_transform : affine00511=(NestedInteger.clearedAll 3 raw00511 (IntegerComputedClassCell.leftNumerator ![(9/640),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/640),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/640),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00511_transform
theorem leaf00511_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00511=true := by decide +kernel
#print axioms leaf00511_sign
theorem leaf00511_log : RationalLog.accepts (1306377687/4294967296) (-2555904525/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00511_log
def leaf00511 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (394430205001/1000000000000) (1306377687/4294967296) (-2555904525/4294967296) 2 8 ![60,0,4] ![(9/640),0,(1/16)] ![(1/3200),1,(1/16)] affine00511
theorem leaf00511_checked : FastNestedCellData.accepts 1 2 4 leaf00511=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (394430205001/1000000000000) (1306377687/4294967296) (-2555904525/4294967296) 2 8 ![60,0,4] ![(9/640),0,(1/16)] ![(1/3200),1,(1/16)] 7275953046594240298430670831616000000000000 3085997444596598951286516021600794393444352 7823937937483198106871741284352000000000000 raw00511 affine00511
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00511_raw leaf00511_rectangular
    leaf00511_transform leaf00511_sign leaf00511_log
#print axioms leaf00511_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
