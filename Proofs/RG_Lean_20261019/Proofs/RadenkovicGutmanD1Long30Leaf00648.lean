/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00648 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3220783890272722254141379837952000000000000 2226215423323480608591480190945828131569664 12750444477513791423688644493312000000000000))
theorem leaf00648_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3220783890272722254141379837952000000000000 2226215423323480608591480190945828131569664 12750444477513791423688644493312000000000000 raw00648=true := by decide +kernel
#print axioms leaf00648_raw
theorem leaf00648_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00648=true := by decide +kernel
#print axioms leaf00648_rectangular
def affine00648 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00648 (IntegerComputedClassCell.leftNumerator ![(19/800),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/800),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/800),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00648_transform : affine00648=(NestedInteger.clearedAll 3 raw00648 (IntegerComputedClassCell.leftNumerator ![(19/800),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/800),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/800),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00648_transform
theorem leaf00648_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00648=true := by decide +kernel
#print axioms leaf00648_sign
theorem leaf00648_log : RationalLog.accepts (2527410701/4294967296) (-1138700235/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00648_log
def leaf00648 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (174599044547/1000000000000) (2527410701/4294967296) (-1138700235/4294967296) 1 8 ![60,0,4] ![(19/800),0,(1/4)] ![(3/6400),1,(1/4)] affine00648
theorem leaf00648_checked : FastNestedCellData.accepts 1 2 4 leaf00648=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (174599044547/1000000000000) (2527410701/4294967296) (-1138700235/4294967296) 1 8 ![60,0,4] ![(19/800),0,(1/4)] ![(3/6400),1,(1/4)] 3220783890272722254141379837952000000000000 2226215423323480608591480190945828131569664 12750444477513791423688644493312000000000000 raw00648 affine00648
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00648_raw leaf00648_rectangular
    leaf00648_transform leaf00648_sign leaf00648_log
#print axioms leaf00648_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
