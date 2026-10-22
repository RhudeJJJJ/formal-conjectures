/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00471 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 101053282245627325121002733568000000000000 47178907145715302590536519319765641068544 134566575680174095708247293952000000000000))
theorem leaf00471_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 101053282245627325121002733568000000000000 47178907145715302590536519319765641068544 134566575680174095708247293952000000000000 raw00471=true := by decide +kernel
#print axioms leaf00471_raw
theorem leaf00471_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00471=true := by decide +kernel
#print axioms leaf00471_rectangular
def affine00471 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00471 (IntegerComputedClassCell.leftNumerator ![(39/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(39/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(39/3200),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00471_transform : affine00471=(NestedInteger.clearedAll 3 raw00471 (IntegerComputedClassCell.leftNumerator ![(39/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(39/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(39/3200),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00471_transform
theorem leaf00471_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00471=true := by decide +kernel
#print axioms leaf00471_sign
theorem leaf00471_log : RationalLog.accepts (1484673269/4294967296) (-285145361/536870912) 2 8=true := by decide +kernel
#print axioms leaf00471_log
def leaf00471 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (43824875259/125000000000) (1484673269/4294967296) (-285145361/536870912) 2 8 ![60,0,4] ![(39/3200),0,(1/16)] ![(1/6400),1,(1/16)] affine00471
theorem leaf00471_checked : FastNestedCellData.accepts 1 2 4 leaf00471=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (43824875259/125000000000) (1484673269/4294967296) (-285145361/536870912) 2 8 ![60,0,4] ![(39/3200),0,(1/16)] ![(1/6400),1,(1/16)] 101053282245627325121002733568000000000000 47178907145715302590536519319765641068544 134566575680174095708247293952000000000000 raw00471 affine00471
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00471_raw leaf00471_rectangular
    leaf00471_transform leaf00471_sign leaf00471_log
#print axioms leaf00471_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
