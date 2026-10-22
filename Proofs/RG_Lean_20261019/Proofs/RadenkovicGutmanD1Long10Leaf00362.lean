/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00362 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 432710358456021615799389126656000000000000 347334818792785589516949537586238447419392 925445333256621128661841477632000000000000))
theorem leaf00362_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 432710358456021615799389126656000000000000 347334818792785589516949537586238447419392 925445333256621128661841477632000000000000 raw00362=true := by decide +kernel
#print axioms leaf00362_raw
theorem leaf00362_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00362=true := by decide +kernel
#print axioms leaf00362_rectangular
def affine00362 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00362 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/32),0,(1/2)] ![(3/160),1,(1/2)]))
theorem leaf00362_transform : affine00362=(NestedInteger.clearedAll 3 raw00362 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/32),0,(1/2)] ![(3/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00362_transform
theorem leaf00362_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00362=true := by decide +kernel
#print axioms leaf00362_sign
theorem leaf00362_log : RationalLog.accepts (2506734087/4294967296) (-1156340943/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00362_log
def leaf00362 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (93829102139/250000000000) (2506734087/4294967296) (-1156340943/4294967296) 1 8 ![52,0,4] ![(7/32),0,(1/2)] ![(3/160),1,(1/2)] affine00362
theorem leaf00362_checked : FastNestedCellData.accepts 1 0 4 leaf00362=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (93829102139/250000000000) (2506734087/4294967296) (-1156340943/4294967296) 1 8 ![52,0,4] ![(7/32),0,(1/2)] ![(3/160),1,(1/2)] 432710358456021615799389126656000000000000 347334818792785589516949537586238447419392 925445333256621128661841477632000000000000 raw00362 affine00362
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00362_raw leaf00362_rectangular
    leaf00362_transform leaf00362_sign leaf00362_log
#print axioms leaf00362_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
