/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00149 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 222349598901235445812841938944000000000000 216057327367328286601611510797668662116352 17924719643704482395022979760128000000000000))
theorem leaf00149_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 222349598901235445812841938944000000000000 216057327367328286601611510797668662116352 17924719643704482395022979760128000000000000 raw00149=true := by decide +kernel
#print axioms leaf00149_raw
theorem leaf00149_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00149=true := by decide +kernel
#print axioms leaf00149_rectangular
def affine00149 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00149 (IntegerComputedClassCell.leftNumerator ![(103/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(103/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(103/32000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00149_transform : affine00149=(NestedInteger.clearedAll 3 raw00149 (IntegerComputedClassCell.leftNumerator ![(103/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(103/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(103/32000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00149_transform
theorem leaf00149_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00149=true := by decide +kernel
#print axioms leaf00149_sign
theorem leaf00149_log : RationalLog.accepts (4123718377/4294967296) (-87378281/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00149_log
def leaf00149 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (12053595909/1000000000000) (4123718377/4294967296) (-87378281/4294967296) 1 8 ![60,0,4] ![(103/32000),0,(1/2)] ![(3/32000),1,(1/2)] affine00149
theorem leaf00149_checked : FastNestedCellData.accepts 1 2 4 leaf00149=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (12053595909/1000000000000) (4123718377/4294967296) (-87378281/4294967296) 1 8 ![60,0,4] ![(103/32000),0,(1/2)] ![(3/32000),1,(1/2)] 222349598901235445812841938944000000000000 216057327367328286601611510797668662116352 17924719643704482395022979760128000000000000 raw00149 affine00149
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00149_raw leaf00149_rectangular
    leaf00149_transform leaf00149_sign leaf00149_log
#print axioms leaf00149_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
