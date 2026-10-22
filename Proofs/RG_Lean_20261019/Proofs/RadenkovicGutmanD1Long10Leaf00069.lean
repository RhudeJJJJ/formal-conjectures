/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00069 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3244558225958573891237101699072000000000000 1746731662486000141453587967090987368448 9930939653211159852633554944000000000000))
theorem leaf00069_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3244558225958573891237101699072000000000000 1746731662486000141453587967090987368448 9930939653211159852633554944000000000000 raw00069=true := by decide +kernel
#print axioms leaf00069_raw
theorem leaf00069_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00069=true := by decide +kernel
#print axioms leaf00069_rectangular
def affine00069 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00069 (IntegerComputedClassCell.leftNumerator ![(3/400),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/400),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/400),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00069_transform : affine00069=(NestedInteger.clearedAll 3 raw00069 (IntegerComputedClassCell.leftNumerator ![(3/400),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/400),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/400),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00069_transform
theorem leaf00069_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00069=true := by decide +kernel
#print axioms leaf00069_sign
theorem leaf00069_log : RationalLog.accepts (1966367/4294967296) (-4128006745/1073741824) 12 8=true := by decide +kernel
#print axioms leaf00069_log
def leaf00069 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (175887853867/1000000000000) (1966367/4294967296) (-4128006745/1073741824) 12 8 ![52,0,4] ![(3/400),0,0] ![(1/3200),1,(1/4)] affine00069
theorem leaf00069_checked : FastNestedCellData.accepts 1 0 4 leaf00069=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (175887853867/1000000000000) (1966367/4294967296) (-4128006745/1073741824) 12 8 ![52,0,4] ![(3/400),0,0] ![(1/3200),1,(1/4)] 3244558225958573891237101699072000000000000 1746731662486000141453587967090987368448 9930939653211159852633554944000000000000 raw00069 affine00069
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00069_raw leaf00069_rectangular
    leaf00069_transform leaf00069_sign leaf00069_log
#print axioms leaf00069_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
