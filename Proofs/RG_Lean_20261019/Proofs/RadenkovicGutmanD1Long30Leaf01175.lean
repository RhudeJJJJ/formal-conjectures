/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01175 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 26443273156587693713646629683200000000000 32501010778510042908925693379350383034368 906904110422034092013360093593600000000000))
theorem leaf01175_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 26443273156587693713646629683200000000000 32501010778510042908925693379350383034368 906904110422034092013360093593600000000000 raw01175=true := by decide +kernel
#print axioms leaf01175_raw
theorem leaf01175_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01175=true := by decide +kernel
#print axioms leaf01175_rectangular
def affine01175 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01175 (IntegerComputedClassCell.leftNumerator ![(1/2),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/2),0,0] ![(1/16),1,(1/2)]))
theorem leaf01175_transform : affine01175=(NestedInteger.clearedAll 3 raw01175 (IntegerComputedClassCell.leftNumerator ![(1/2),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/2),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf01175_transform
theorem leaf01175_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01175=true := by decide +kernel
#print axioms leaf01175_sign
theorem leaf01175_log : RationalLog.accepts (5096241083/4294967296) (45918377/536870912) 0 8=true := by decide +kernel
#print axioms leaf01175_log
def leaf01175 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (7167463551/200000000000) (5096241083/4294967296) (45918377/536870912) 0 8 ![60,0,4] ![(1/2),0,0] ![(1/16),1,(1/2)] affine01175
theorem leaf01175_checked : FastNestedCellData.accepts 1 2 4 leaf01175=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (7167463551/200000000000) (5096241083/4294967296) (45918377/536870912) 0 8 ![60,0,4] ![(1/2),0,0] ![(1/16),1,(1/2)] 26443273156587693713646629683200000000000 32501010778510042908925693379350383034368 906904110422034092013360093593600000000000 raw01175 affine01175
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01175_raw leaf01175_rectangular
    leaf01175_transform leaf01175_sign leaf01175_log
#print axioms leaf01175_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
