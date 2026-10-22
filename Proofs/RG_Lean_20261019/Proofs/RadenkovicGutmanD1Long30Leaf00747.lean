/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00747 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 121143186843463034159744679936000000000000 52764694502427662053873465894976599621632 125540594896324013549607190528000000000000))
theorem leaf00747_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 121143186843463034159744679936000000000000 52764694502427662053873465894976599621632 125540594896324013549607190528000000000000 raw00747=true := by decide +kernel
#print axioms leaf00747_raw
theorem leaf00747_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00747=true := by decide +kernel
#print axioms leaf00747_rectangular
def affine00747 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00747 (IntegerComputedClassCell.leftNumerator ![(53/1600),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(53/1600),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(53/1600),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00747_transform : affine00747=(NestedInteger.clearedAll 3 raw00747 (IntegerComputedClassCell.leftNumerator ![(53/1600),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(53/1600),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(53/1600),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00747_transform
theorem leaf00747_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00747=true := by decide +kernel
#print axioms leaf00747_sign
theorem leaf00747_log : RationalLog.accepts (1317116683/4294967296) (-2538323433/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00747_log
def leaf00747 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (52537482543/125000000000) (1317116683/4294967296) (-2538323433/4294967296) 2 8 ![60,0,4] ![(53/1600),0,(1/8)] ![(3/6400),1,(1/8)] affine00747
theorem leaf00747_checked : FastNestedCellData.accepts 1 2 4 leaf00747=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (52537482543/125000000000) (1317116683/4294967296) (-2538323433/4294967296) 2 8 ![60,0,4] ![(53/1600),0,(1/8)] ![(3/6400),1,(1/8)] 121143186843463034159744679936000000000000 52764694502427662053873465894976599621632 125540594896324013549607190528000000000000 raw00747 affine00747
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00747_raw leaf00747_rectangular
    leaf00747_transform leaf00747_sign leaf00747_log
#print axioms leaf00747_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
