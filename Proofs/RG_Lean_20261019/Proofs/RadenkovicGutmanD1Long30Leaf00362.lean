/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00362 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 311345884666647017641622896640000000000 230541136300420451177144782933284880384 1707399049271752645045072691200000000000))
theorem leaf00362_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 311345884666647017641622896640000000000 230541136300420451177144782933284880384 1707399049271752645045072691200000000000 raw00362=true := by decide +kernel
#print axioms leaf00362_raw
theorem leaf00362_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00362=true := by decide +kernel
#print axioms leaf00362_rectangular
def affine00362 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00362 (IntegerComputedClassCell.leftNumerator ![(7/800),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/800),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/800),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00362_transform : affine00362=(NestedInteger.clearedAll 3 raw00362 (IntegerComputedClassCell.leftNumerator ![(7/800),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/800),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/800),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00362_transform
theorem leaf00362_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00362=true := by decide +kernel
#print axioms leaf00362_sign
theorem leaf00362_log : RationalLog.accepts (1400973215/2147483648) (-917253893/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00362_log
def leaf00362 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (6751237691/50000000000) (1400973215/2147483648) (-917253893/4294967296) 1 8 ![60,0,4] ![(7/800),0,(1/8)] ![(1/6400),1,(1/8)] affine00362
theorem leaf00362_checked : FastNestedCellData.accepts 1 2 4 leaf00362=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (6751237691/50000000000) (1400973215/2147483648) (-917253893/4294967296) 1 8 ![60,0,4] ![(7/800),0,(1/8)] ![(1/6400),1,(1/8)] 311345884666647017641622896640000000000 230541136300420451177144782933284880384 1707399049271752645045072691200000000000 raw00362 affine00362
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00362_raw leaf00362_rectangular
    leaf00362_transform leaf00362_sign leaf00362_log
#print axioms leaf00362_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
