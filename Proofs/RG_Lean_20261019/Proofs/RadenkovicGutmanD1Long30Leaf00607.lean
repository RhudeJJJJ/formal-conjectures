/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00607 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 266273037402403635550455909580800000000000 144701438426730495071044575500118937042944 501228067962739015221923282944000000000000))
theorem leaf00607_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 266273037402403635550455909580800000000000 144701438426730495071044575500118937042944 501228067962739015221923282944000000000000 raw00607=true := by decide +kernel
#print axioms leaf00607_raw
theorem leaf00607_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00607=true := by decide +kernel
#print axioms leaf00607_rectangular
def affine00607 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00607 (IntegerComputedClassCell.leftNumerator ![(1/50),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/50),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/50),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00607_transform : affine00607=(NestedInteger.clearedAll 3 raw00607 (IntegerComputedClassCell.leftNumerator ![(1/50),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/50),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/50),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00607_transform
theorem leaf00607_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00607=true := by decide +kernel
#print axioms leaf00607_sign
theorem leaf00607_log : RationalLog.accepts (1811155655/4294967296) (-1854306709/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00607_log
def leaf00607 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (144346902813/500000000000) (1811155655/4294967296) (-1854306709/4294967296) 2 8 ![60,0,4] ![(1/50),0,(1/8)] ![(3/6400),1,(1/8)] affine00607
theorem leaf00607_checked : FastNestedCellData.accepts 1 2 4 leaf00607=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (144346902813/500000000000) (1811155655/4294967296) (-1854306709/4294967296) 2 8 ![60,0,4] ![(1/50),0,(1/8)] ![(3/6400),1,(1/8)] 266273037402403635550455909580800000000000 144701438426730495071044575500118937042944 501228067962739015221923282944000000000000 raw00607 affine00607
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00607_raw leaf00607_rectangular
    leaf00607_transform leaf00607_sign leaf00607_log
#print axioms leaf00607_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
