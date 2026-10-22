/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00407 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 700778579504493943582621696000000000000 497220084152441020705752086292218249216 3195417570116667668500054016000000000000))
theorem leaf00407_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 700778579504493943582621696000000000000 497220084152441020705752086292218249216 3195417570116667668500054016000000000000 raw00407=true := by decide +kernel
#print axioms leaf00407_raw
theorem leaf00407_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00407=true := by decide +kernel
#print axioms leaf00407_rectangular
def affine00407 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00407 (IntegerComputedClassCell.leftNumerator ![(13/1280),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/1280),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/1280),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00407_transform : affine00407=(NestedInteger.clearedAll 3 raw00407 (IntegerComputedClassCell.leftNumerator ![(13/1280),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/1280),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/1280),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00407_transform
theorem leaf00407_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00407=true := by decide +kernel
#print axioms leaf00407_sign
theorem leaf00407_log : RationalLog.accepts (82407863/134217728) (-261876223/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00407_log
def leaf00407 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (77802051413/500000000000) (82407863/134217728) (-261876223/1073741824) 1 8 ![60,0,4] ![(13/1280),0,(1/8)] ![(1/6400),1,(1/8)] affine00407
theorem leaf00407_checked : FastNestedCellData.accepts 1 2 4 leaf00407=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (77802051413/500000000000) (82407863/134217728) (-261876223/1073741824) 1 8 ![60,0,4] ![(13/1280),0,(1/8)] ![(1/6400),1,(1/8)] 700778579504493943582621696000000000000 497220084152441020705752086292218249216 3195417570116667668500054016000000000000 raw00407 affine00407
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00407_raw leaf00407_rectangular
    leaf00407_transform leaf00407_sign leaf00407_log
#print axioms leaf00407_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
