/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01035 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 148814186462852384535781310464000000000000 112592461612001787285082444344895647776768 218074421086025858907927216128000000000000))
theorem leaf01035_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 148814186462852384535781310464000000000000 112592461612001787285082444344895647776768 218074421086025858907927216128000000000000 raw01035=true := by decide +kernel
#print axioms leaf01035_raw
theorem leaf01035_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01035=true := by decide +kernel
#print axioms leaf01035_rectangular
def affine01035 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01035 (IntegerComputedClassCell.leftNumerator ![(7/32),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/32),0,0] ![(3/160),1,(1/16)]))
theorem leaf01035_transform : affine01035=(NestedInteger.clearedAll 3 raw01035 (IntegerComputedClassCell.leftNumerator ![(7/32),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/32),0,0] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01035_transform
theorem leaf01035_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01035=true := by decide +kernel
#print axioms leaf01035_sign
theorem leaf01035_log : RationalLog.accepts (267885299/536870912) (-1492928081/4294967296) 2 8=true := by decide +kernel
#print axioms leaf01035_log
def leaf01035 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (516302925631/1000000000000) (267885299/536870912) (-1492928081/4294967296) 2 8 ![60,0,4] ![(7/32),0,0] ![(3/160),1,(1/16)] affine01035
theorem leaf01035_checked : FastNestedCellData.accepts 1 2 4 leaf01035=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (516302925631/1000000000000) (267885299/536870912) (-1492928081/4294967296) 2 8 ![60,0,4] ![(7/32),0,0] ![(3/160),1,(1/16)] 148814186462852384535781310464000000000000 112592461612001787285082444344895647776768 218074421086025858907927216128000000000000 raw01035 affine01035
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01035_raw leaf01035_rectangular
    leaf01035_transform leaf01035_sign leaf01035_log
#print axioms leaf01035_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
