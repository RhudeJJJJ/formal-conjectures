/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00892 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10327112169224782969120489472000000000000 3985707054666158658491175037493626011648 6952584037847207639468998656000000000000))
theorem leaf00892_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10327112169224782969120489472000000000000 3985707054666158658491175037493626011648 6952584037847207639468998656000000000000 raw00892=true := by decide +kernel
#print axioms leaf00892_raw
theorem leaf00892_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00892=true := by decide +kernel
#print axioms leaf00892_rectangular
def affine00892 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00892 (IntegerComputedClassCell.leftNumerator ![(21/320),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(21/320),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(21/320),0,(1/8)] ![(1/640),1,(1/8)]))
theorem leaf00892_transform : affine00892=(NestedInteger.clearedAll 3 raw00892 (IntegerComputedClassCell.leftNumerator ![(21/320),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(21/320),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(21/320),0,(1/8)] ![(1/640),1,(1/8)])) := by decide +kernel
#print axioms leaf00892_transform
theorem leaf00892_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00892=true := by decide +kernel
#print axioms leaf00892_sign
theorem leaf00892_log : RationalLog.accepts (1053617833/4294967296) (-377209313/536870912) 3 8=true := by decide +kernel
#print axioms leaf00892_log
def leaf00892 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (17914683919/31250000000) (1053617833/4294967296) (-377209313/536870912) 3 8 ![60,0,4] ![(21/320),0,(1/8)] ![(1/640),1,(1/8)] affine00892
theorem leaf00892_checked : FastNestedCellData.accepts 1 2 4 leaf00892=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (17914683919/31250000000) (1053617833/4294967296) (-377209313/536870912) 3 8 ![60,0,4] ![(21/320),0,(1/8)] ![(1/640),1,(1/8)] 10327112169224782969120489472000000000000 3985707054666158658491175037493626011648 6952584037847207639468998656000000000000 raw00892 affine00892
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00892_raw leaf00892_rectangular
    leaf00892_transform leaf00892_sign leaf00892_log
#print axioms leaf00892_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
