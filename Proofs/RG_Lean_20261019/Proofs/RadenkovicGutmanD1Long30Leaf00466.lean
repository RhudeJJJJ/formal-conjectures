/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00466 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1279912613064380349917965372620800000000000 602133204147009056007051364903408361275392 1735649293835636944108328583168000000000000))
theorem leaf00466_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1279912613064380349917965372620800000000000 602133204147009056007051364903408361275392 1735649293835636944108328583168000000000000 raw00466=true := by decide +kernel
#print axioms leaf00466_raw
theorem leaf00466_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00466=true := by decide +kernel
#print axioms leaf00466_rectangular
def affine00466 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00466 (IntegerComputedClassCell.leftNumerator ![(77/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(77/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(77/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00466_transform : affine00466=(NestedInteger.clearedAll 3 raw00466 (IntegerComputedClassCell.leftNumerator ![(77/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(77/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(77/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00466_transform
theorem leaf00466_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00466=true := by decide +kernel
#print axioms leaf00466_sign
theorem leaf00466_log : RationalLog.accepts (1500133785/4294967296) (-2258915887/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00466_log
def leaf00466 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (346921008919/1000000000000) (1500133785/4294967296) (-2258915887/4294967296) 2 8 ![60,0,4] ![(77/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00466
theorem leaf00466_checked : FastNestedCellData.accepts 1 2 4 leaf00466=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (346921008919/1000000000000) (1500133785/4294967296) (-2258915887/4294967296) 2 8 ![60,0,4] ![(77/6400),0,(1/16)] ![(1/6400),1,(1/16)] 1279912613064380349917965372620800000000000 602133204147009056007051364903408361275392 1735649293835636944108328583168000000000000 raw00466 affine00466
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00466_raw leaf00466_rectangular
    leaf00466_transform leaf00466_sign leaf00466_log
#print axioms leaf00466_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
