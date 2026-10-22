/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00653 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7317068069798638079262588928000000000000 5029433713873006567823648004378797801472 28302428501053398386850398208000000000000))
theorem leaf00653_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7317068069798638079262588928000000000000 5029433713873006567823648004378797801472 28302428501053398386850398208000000000000 raw00653=true := by decide +kernel
#print axioms leaf00653_raw
theorem leaf00653_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00653=true := by decide +kernel
#print axioms leaf00653_rectangular
def affine00653 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00653 (IntegerComputedClassCell.leftNumerator ![(31/1280),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/1280),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/1280),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00653_transform : affine00653=(NestedInteger.clearedAll 3 raw00653 (IntegerComputedClassCell.leftNumerator ![(31/1280),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/1280),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/1280),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00653_transform
theorem leaf00653_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00653=true := by decide +kernel
#print axioms leaf00653_sign
theorem leaf00653_log : RationalLog.accepts (2506720881/4294967296) (-1156352257/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00653_log
def leaf00653 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (22212907073/125000000000) (2506720881/4294967296) (-1156352257/4294967296) 1 8 ![60,0,4] ![(31/1280),0,(1/4)] ![(3/6400),1,(1/4)] affine00653
theorem leaf00653_checked : FastNestedCellData.accepts 1 2 4 leaf00653=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (22212907073/125000000000) (2506720881/4294967296) (-1156352257/4294967296) 1 8 ![60,0,4] ![(31/1280),0,(1/4)] ![(3/6400),1,(1/4)] 7317068069798638079262588928000000000000 5029433713873006567823648004378797801472 28302428501053398386850398208000000000000 raw00653 affine00653
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00653_raw leaf00653_rectangular
    leaf00653_transform leaf00653_sign leaf00653_log
#print axioms leaf00653_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
