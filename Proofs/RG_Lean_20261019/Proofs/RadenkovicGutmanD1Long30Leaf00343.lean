/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00343 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 71662111108515402703400075264000000000000 62199789756557668620850667653608480178176 1000688844956993556879438249984000000000000))
theorem leaf00343_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 71662111108515402703400075264000000000000 62199789756557668620850667653608480178176 1000688844956993556879438249984000000000000 raw00343=true := by decide +kernel
#print axioms leaf00343_raw
theorem leaf00343_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00343=true := by decide +kernel
#print axioms leaf00343_rectangular
def affine00343 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00343 (IntegerComputedClassCell.leftNumerator ![(13/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/1600),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00343_transform : affine00343=(NestedInteger.clearedAll 3 raw00343 (IntegerComputedClassCell.leftNumerator ![(13/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/1600),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00343_transform
theorem leaf00343_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00343=true := by decide +kernel
#print axioms leaf00343_sign
theorem leaf00343_log : RationalLog.accepts (877425969/1073741824) (-108400835/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00343_log
def leaf00343 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (62156973239/1000000000000) (877425969/1073741824) (-108400835/1073741824) 1 8 ![60,0,4] ![(13/1600),0,(1/4)] ![(1/6400),1,(1/4)] affine00343
theorem leaf00343_checked : FastNestedCellData.accepts 1 2 4 leaf00343=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (62156973239/1000000000000) (877425969/1073741824) (-108400835/1073741824) 1 8 ![60,0,4] ![(13/1600),0,(1/4)] ![(1/6400),1,(1/4)] 71662111108515402703400075264000000000000 62199789756557668620850667653608480178176 1000688844956993556879438249984000000000000 raw00343 affine00343
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00343_raw leaf00343_rectangular
    leaf00343_transform leaf00343_sign leaf00343_log
#print axioms leaf00343_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
