/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00256 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 789429574032183770123234967552000000000000 536973533709550174942209457420051597492224 3136889494809987036947622658048000000000000))
theorem leaf00256_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 789429574032183770123234967552000000000000 536973533709550174942209457420051597492224 3136889494809987036947622658048000000000000 raw00256=true := by decide +kernel
#print axioms leaf00256_raw
theorem leaf00256_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00256=true := by decide +kernel
#print axioms leaf00256_rectangular
def affine00256 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00256 (IntegerComputedClassCell.leftNumerator ![(7/1280),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/1280),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/1280),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00256_transform : affine00256=(NestedInteger.clearedAll 3 raw00256 (IntegerComputedClassCell.leftNumerator ![(7/1280),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/1280),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/1280),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00256_transform
theorem leaf00256_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00256=true := by decide +kernel
#print axioms leaf00256_sign
theorem leaf00256_log : RationalLog.accepts (2494454629/4294967296) (-36465201/134217728) 1 8=true := by decide +kernel
#print axioms leaf00256_log
def leaf00256 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (85590125919/500000000000) (2494454629/4294967296) (-36465201/134217728) 1 8 ![60,0,4] ![(7/1280),0,(1/16)] ![(1/6400),1,(1/16)] affine00256
theorem leaf00256_checked : FastNestedCellData.accepts 1 2 4 leaf00256=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (85590125919/500000000000) (2494454629/4294967296) (-36465201/134217728) 1 8 ![60,0,4] ![(7/1280),0,(1/16)] ![(1/6400),1,(1/16)] 789429574032183770123234967552000000000000 536973533709550174942209457420051597492224 3136889494809987036947622658048000000000000 raw00256 affine00256
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00256_raw leaf00256_rectangular
    leaf00256_transform leaf00256_sign leaf00256_log
#print axioms leaf00256_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
