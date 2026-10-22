/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00725 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1010257655842913611685967167488000000000000 36598533249606811478682045940700631007232 41766806493868727000014782464000000000000))
theorem leaf00725_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1010257655842913611685967167488000000000000 36598533249606811478682045940700631007232 41766806493868727000014782464000000000000 raw00725=true := by decide +kernel
#print axioms leaf00725_raw
theorem leaf00725_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00725=true := by decide +kernel
#print axioms leaf00725_rectangular
def affine00725 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00725 (IntegerComputedClassCell.leftNumerator ![(1/32),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/32),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00725_transform : affine00725=(NestedInteger.clearedAll 3 raw00725 (IntegerComputedClassCell.leftNumerator ![(1/32),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/32),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00725_transform
theorem leaf00725_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00725=true := by decide +kernel
#print axioms leaf00725_sign
theorem leaf00725_log : RationalLog.accepts (82927513/4294967296) (-4238308549/2147483648) 6 8=true := by decide +kernel
#print axioms leaf00725_log
def leaf00725 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (219064709047/250000000000) (82927513/4294967296) (-4238308549/2147483648) 6 8 ![60,0,4] ![(1/32),0,0] ![(3/6400),1,(1/16)] affine00725
theorem leaf00725_checked : FastNestedCellData.accepts 1 2 4 leaf00725=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (219064709047/250000000000) (82927513/4294967296) (-4238308549/2147483648) 6 8 ![60,0,4] ![(1/32),0,0] ![(3/6400),1,(1/16)] 1010257655842913611685967167488000000000000 36598533249606811478682045940700631007232 41766806493868727000014782464000000000000 raw00725 affine00725
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00725_raw leaf00725_rectangular
    leaf00725_transform leaf00725_sign leaf00725_log
#print axioms leaf00725_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
