/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01021 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 618489694259256437875146752000000000000 422218942110849907492672496274895798272 768608227432372600112676864000000000000))
theorem leaf01021_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 618489694259256437875146752000000000000 422218942110849907492672496274895798272 768608227432372600112676864000000000000 raw01021=true := by decide +kernel
#print axioms leaf01021_raw
theorem leaf01021_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01021=true := by decide +kernel
#print axioms leaf01021_rectangular
def affine01021 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01021 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(1/16)] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(1/16)] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/16),0,(1/16)] ![(1/80),1,(1/16)]))
theorem leaf01021_transform : affine01021=(NestedInteger.clearedAll 3 raw01021 (IntegerComputedClassCell.leftNumerator ![(3/16),0,(1/16)] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,(1/16)] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/16),0,(1/16)] ![(1/80),1,(1/16)])) := by decide +kernel
#print axioms leaf01021_transform
theorem leaf01021_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01021=true := by decide +kernel
#print axioms leaf01021_sign
theorem leaf01021_log : RationalLog.accepts (236554609/536870912) (-110001981/268435456) 2 8=true := by decide +kernel
#print axioms leaf01021_log
def leaf01021 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (34333074953/62500000000) (236554609/536870912) (-110001981/268435456) 2 8 ![60,0,4] ![(3/16),0,(1/16)] ![(1/80),1,(1/16)] affine01021
theorem leaf01021_checked : FastNestedCellData.accepts 1 2 4 leaf01021=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (34333074953/62500000000) (236554609/536870912) (-110001981/268435456) 2 8 ![60,0,4] ![(3/16),0,(1/16)] ![(1/80),1,(1/16)] 618489694259256437875146752000000000000 422218942110849907492672496274895798272 768608227432372600112676864000000000000 raw01021 affine01021
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01021_raw leaf01021_rectangular
    leaf01021_transform leaf01021_sign leaf01021_log
#print axioms leaf01021_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
