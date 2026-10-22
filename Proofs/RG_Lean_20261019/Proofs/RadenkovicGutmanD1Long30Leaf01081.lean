/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01081 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5619820878768311529475818913792000000000000 5961305613929701372249307454038259659702272 19567648396194158768970746822656000000000000))
theorem leaf01081_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5619820878768311529475818913792000000000000 5961305613929701372249307454038259659702272 19567648396194158768970746822656000000000000 raw01081=true := by decide +kernel
#print axioms leaf01081_raw
theorem leaf01081_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01081=true := by decide +kernel
#print axioms leaf01081_rectangular
def affine01081 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01081 (IntegerComputedClassCell.leftNumerator ![(31/80),0,(1/16)] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/80),0,(1/16)] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/80),0,(1/16)] ![(3/80),1,(1/16)]))
theorem leaf01081_transform : affine01081=(NestedInteger.clearedAll 3 raw01081 (IntegerComputedClassCell.leftNumerator ![(31/80),0,(1/16)] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/80),0,(1/16)] ![(3/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/80),0,(1/16)] ![(3/80),1,(1/16)])) := by decide +kernel
#print axioms leaf01081_transform
theorem leaf01081_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01081=true := by decide +kernel
#print axioms leaf01081_sign
theorem leaf01081_log : RationalLog.accepts (3492081653/4294967296) (-55551627/536870912) 1 8=true := by decide +kernel
#print axioms leaf01081_log
def leaf01081 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (304651100287/1000000000000) (3492081653/4294967296) (-55551627/536870912) 1 8 ![60,0,4] ![(31/80),0,(1/16)] ![(3/80),1,(1/16)] affine01081
theorem leaf01081_checked : FastNestedCellData.accepts 1 2 4 leaf01081=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (304651100287/1000000000000) (3492081653/4294967296) (-55551627/536870912) 1 8 ![60,0,4] ![(31/80),0,(1/16)] ![(3/80),1,(1/16)] 5619820878768311529475818913792000000000000 5961305613929701372249307454038259659702272 19567648396194158768970746822656000000000000 raw01081 affine01081
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01081_raw leaf01081_rectangular
    leaf01081_transform leaf01081_sign leaf01081_log
#print axioms leaf01081_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
