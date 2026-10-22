/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00341 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 284775515905109461753881690112000000000000 165025348538092735919158408096841925132288 668109660095232686243104948224000000000000))
theorem leaf00341_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 284775515905109461753881690112000000000000 165025348538092735919158408096841925132288 668109660095232686243104948224000000000000 raw00341=true := by decide +kernel
#print axioms leaf00341_raw
theorem leaf00341_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00341=true := by decide +kernel
#print axioms leaf00341_rectangular
def affine00341 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00341 (IntegerComputedClassCell.leftNumerator ![(13/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/1600),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00341_transform : affine00341=(NestedInteger.clearedAll 3 raw00341 (IntegerComputedClassCell.leftNumerator ![(13/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/1600),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00341_transform
theorem leaf00341_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00341=true := by decide +kernel
#print axioms leaf00341_sign
theorem leaf00341_log : RationalLog.accepts (1995906717/4294967296) (-1645714499/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00341_log
def leaf00341 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (61750846603/250000000000) (1995906717/4294967296) (-1645714499/4294967296) 2 8 ![60,0,4] ![(13/1600),0,(1/16)] ![(1/6400),1,(1/16)] affine00341
theorem leaf00341_checked : FastNestedCellData.accepts 1 2 4 leaf00341=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (61750846603/250000000000) (1995906717/4294967296) (-1645714499/4294967296) 2 8 ![60,0,4] ![(13/1600),0,(1/16)] ![(1/6400),1,(1/16)] 284775515905109461753881690112000000000000 165025348538092735919158408096841925132288 668109660095232686243104948224000000000000 raw00341 affine00341
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00341_raw leaf00341_rectangular
    leaf00341_transform leaf00341_sign leaf00341_log
#print axioms leaf00341_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
