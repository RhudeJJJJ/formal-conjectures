/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00339 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7292705095650149038949820006400000000000 6807437185434870363958888416369772068864 229590254755576645382883298508800000000000))
theorem leaf00339_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7292705095650149038949820006400000000000 6807437185434870363958888416369772068864 229590254755576645382883298508800000000000 raw00339=true := by decide +kernel
#print axioms leaf00339_raw
theorem leaf00339_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00339=true := by decide +kernel
#print axioms leaf00339_rectangular
def affine00339 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00339 (IntegerComputedClassCell.leftNumerator ![(51/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(51/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(51/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00339_transform : affine00339=(NestedInteger.clearedAll 3 raw00339 (IntegerComputedClassCell.leftNumerator ![(51/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(51/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(51/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00339_transform
theorem leaf00339_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00339=true := by decide +kernel
#print axioms leaf00339_sign
theorem leaf00339_log : RationalLog.accepts (3893723157/4294967296) (-210621219/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00339_log
def leaf00339 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (5930075031/200000000000) (3893723157/4294967296) (-210621219/4294967296) 1 8 ![60,0,4] ![(51/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00339
theorem leaf00339_checked : FastNestedCellData.accepts 1 2 4 leaf00339=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (5930075031/200000000000) (3893723157/4294967296) (-210621219/4294967296) 1 8 ![60,0,4] ![(51/6400),0,(1/2)] ![(1/6400),1,(1/2)] 7292705095650149038949820006400000000000 6807437185434870363958888416369772068864 229590254755576645382883298508800000000000 raw00339 affine00339
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00339_raw leaf00339_rectangular
    leaf00339_transform leaf00339_sign leaf00339_log
#print axioms leaf00339_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
