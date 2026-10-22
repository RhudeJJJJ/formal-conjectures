/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00661 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 661866265698332315537461215232000000000000 195563208448448573582040875063652105846784 340656474298831884239830515712000000000000))
theorem leaf00661_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 661866265698332315537461215232000000000000 195563208448448573582040875063652105846784 340656474298831884239830515712000000000000 raw00661=true := by decide +kernel
#print axioms leaf00661_raw
theorem leaf00661_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00661=true := by decide +kernel
#print axioms leaf00661_rectangular
def affine00661 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00661 (IntegerComputedClassCell.leftNumerator ![(161/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(161/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(161/6400),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00661_transform : affine00661=(NestedInteger.clearedAll 3 raw00661 (IntegerComputedClassCell.leftNumerator ![(161/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(161/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(161/6400),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00661_transform
theorem leaf00661_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00661=true := by decide +kernel
#print axioms leaf00661_sign
theorem leaf00661_log : RationalLog.accepts (806214611/4294967296) (-898104127/1073741824) 3 8=true := by decide +kernel
#print axioms leaf00661_log
def leaf00661 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (143519368633/250000000000) (806214611/4294967296) (-898104127/1073741824) 3 8 ![60,0,4] ![(161/6400),0,(1/16)] ![(3/6400),1,(1/16)] affine00661
theorem leaf00661_checked : FastNestedCellData.accepts 1 2 4 leaf00661=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (143519368633/250000000000) (806214611/4294967296) (-898104127/1073741824) 3 8 ![60,0,4] ![(161/6400),0,(1/16)] ![(3/6400),1,(1/16)] 661866265698332315537461215232000000000000 195563208448448573582040875063652105846784 340656474298831884239830515712000000000000 raw00661 affine00661
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00661_raw leaf00661_rectangular
    leaf00661_transform leaf00661_sign leaf00661_log
#print axioms leaf00661_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
