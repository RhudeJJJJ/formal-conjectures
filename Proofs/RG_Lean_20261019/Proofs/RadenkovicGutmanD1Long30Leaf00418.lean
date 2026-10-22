/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00418 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 22952205615122676957344432128000000000000 19192948709578970077795659638740847951872 241022188402562774781191520256000000000000))
theorem leaf00418_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 22952205615122676957344432128000000000000 19192948709578970077795659638740847951872 241022188402562774781191520256000000000000 raw00418=true := by decide +kernel
#print axioms leaf00418_raw
theorem leaf00418_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00418=true := by decide +kernel
#print axioms leaf00418_rectangular
def affine00418 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00418 (IntegerComputedClassCell.leftNumerator ![(67/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(67/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(67/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00418_transform : affine00418=(NestedInteger.clearedAll 3 raw00418 (IntegerComputedClassCell.leftNumerator ![(67/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(67/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(67/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00418_transform
theorem leaf00418_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00418=true := by decide +kernel
#print axioms leaf00418_sign
theorem leaf00418_log : RationalLog.accepts (1663303921/2147483648) (-548662399/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00418_log
def leaf00418 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (19907864953/250000000000) (1663303921/2147483648) (-548662399/4294967296) 1 8 ![60,0,4] ![(67/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00418
theorem leaf00418_checked : FastNestedCellData.accepts 1 2 4 leaf00418=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (19907864953/250000000000) (1663303921/2147483648) (-548662399/4294967296) 1 8 ![60,0,4] ![(67/6400),0,(1/4)] ![(1/6400),1,(1/4)] 22952205615122676957344432128000000000000 19192948709578970077795659638740847951872 241022188402562774781191520256000000000000 raw00418 affine00418
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00418_raw leaf00418_rectangular
    leaf00418_transform leaf00418_sign leaf00418_log
#print axioms leaf00418_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
