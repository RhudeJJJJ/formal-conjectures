/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00258 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 38881527839369469399109363302400000000000 35252652740667491580435491498050361229312 836253999216552530189960085504000000000000))
theorem leaf00258_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 38881527839369469399109363302400000000000 35252652740667491580435491498050361229312 836253999216552530189960085504000000000000 raw00258=true := by decide +kernel
#print axioms leaf00258_raw
theorem leaf00258_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00258=true := by decide +kernel
#print axioms leaf00258_rectangular
def affine00258 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00258 (IntegerComputedClassCell.leftNumerator ![(7/1280),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/1280),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/1280),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00258_transform : affine00258=(NestedInteger.clearedAll 3 raw00258 (IntegerComputedClassCell.leftNumerator ![(7/1280),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/1280),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/1280),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00258_transform
theorem leaf00258_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00258=true := by decide +kernel
#print axioms leaf00258_sign
theorem leaf00258_log : RationalLog.accepts (1868296705/2147483648) (-299079219/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00258_log
def leaf00258 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (42155436953/1000000000000) (1868296705/2147483648) (-299079219/4294967296) 1 8 ![60,0,4] ![(7/1280),0,(1/4)] ![(1/6400),1,(1/4)] affine00258
theorem leaf00258_checked : FastNestedCellData.accepts 1 2 4 leaf00258=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (42155436953/1000000000000) (1868296705/2147483648) (-299079219/4294967296) 1 8 ![60,0,4] ![(7/1280),0,(1/4)] ![(1/6400),1,(1/4)] 38881527839369469399109363302400000000000 35252652740667491580435491498050361229312 836253999216552530189960085504000000000000 raw00258 affine00258
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00258_raw leaf00258_rectangular
    leaf00258_transform leaf00258_sign leaf00258_log
#print axioms leaf00258_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
