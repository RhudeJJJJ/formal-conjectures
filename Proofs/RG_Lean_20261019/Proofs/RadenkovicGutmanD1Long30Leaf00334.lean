/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00334 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2438067660333286383139631923200000000000 2278727209618214898648229884548817616896 78368877446984662269909008384000000000000))
theorem leaf00334_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2438067660333286383139631923200000000000 2278727209618214898648229884548817616896 78368877446984662269909008384000000000000 raw00334=true := by decide +kernel
#print axioms leaf00334_raw
theorem leaf00334_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00334=true := by decide +kernel
#print axioms leaf00334_rectangular
def affine00334 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00334 (IntegerComputedClassCell.leftNumerator ![(1/128),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/128),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00334_transform : affine00334=(NestedInteger.clearedAll 3 raw00334 (IntegerComputedClassCell.leftNumerator ![(1/128),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/128),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00334_transform
theorem leaf00334_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00334=true := by decide +kernel
#print axioms leaf00334_sign
theorem leaf00334_log : RationalLog.accepts (3900844145/4294967296) (-206697407/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00334_log
def leaf00334 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (14538470397/500000000000) (3900844145/4294967296) (-206697407/4294967296) 1 8 ![60,0,4] ![(1/128),0,(1/2)] ![(1/6400),1,(1/2)] affine00334
theorem leaf00334_checked : FastNestedCellData.accepts 1 2 4 leaf00334=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (14538470397/500000000000) (3900844145/4294967296) (-206697407/4294967296) 1 8 ![60,0,4] ![(1/128),0,(1/2)] ![(1/6400),1,(1/2)] 2438067660333286383139631923200000000000 2278727209618214898648229884548817616896 78368877446984662269909008384000000000000 raw00334 affine00334
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00334_raw leaf00334_rectangular
    leaf00334_transform leaf00334_sign leaf00334_log
#print axioms leaf00334_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
