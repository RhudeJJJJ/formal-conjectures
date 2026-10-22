/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00846 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 828103302060348736354945859584000000000000 211490548719435691024968551314974591418368 294446358362630952556274122752000000000000))
theorem leaf00846_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 828103302060348736354945859584000000000000 211490548719435691024968551314974591418368 294446358362630952556274122752000000000000 raw00846=true := by decide +kernel
#print axioms leaf00846_raw
theorem leaf00846_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00846=true := by decide +kernel
#print axioms leaf00846_rectangular
def affine00846 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00846 (IntegerComputedClassCell.leftNumerator ![(33/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(33/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(33/640),0,(1/16)] ![(1/640),1,(1/16)]))
theorem leaf00846_transform : affine00846=(NestedInteger.clearedAll 3 raw00846 (IntegerComputedClassCell.leftNumerator ![(33/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(33/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(33/640),0,(1/16)] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00846_transform
theorem leaf00846_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00846=true := by decide +kernel
#print axioms leaf00846_sign
theorem leaf00846_log : RationalLog.accepts (159593847/1073741824) (-4093689617/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00846_log
def leaf00846 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (718265119309/1000000000000) (159593847/1073741824) (-4093689617/4294967296) 3 8 ![60,0,4] ![(33/640),0,(1/16)] ![(1/640),1,(1/16)] affine00846
theorem leaf00846_checked : FastNestedCellData.accepts 1 2 4 leaf00846=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (718265119309/1000000000000) (159593847/1073741824) (-4093689617/4294967296) 3 8 ![60,0,4] ![(33/640),0,(1/16)] ![(1/640),1,(1/16)] 828103302060348736354945859584000000000000 211490548719435691024968551314974591418368 294446358362630952556274122752000000000000 raw00846 affine00846
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00846_raw leaf00846_rectangular
    leaf00846_transform leaf00846_sign leaf00846_log
#print axioms leaf00846_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
