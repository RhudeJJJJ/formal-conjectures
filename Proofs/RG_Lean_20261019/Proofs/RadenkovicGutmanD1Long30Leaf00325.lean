/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00325 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3560840652744233825698960113664000000000000 6194627580111049421241950538444683870208 10696978676855066930114985984000000000000))
theorem leaf00325_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3560840652744233825698960113664000000000000 6194627580111049421241950538444683870208 10696978676855066930114985984000000000000 raw00325=true := by decide +kernel
#print axioms leaf00325_raw
theorem leaf00325_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00325=true := by decide +kernel
#print axioms leaf00325_rectangular
def affine00325 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00325 (IntegerComputedClassCell.leftNumerator ![(49/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(49/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(49/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00325_transform : affine00325=(NestedInteger.clearedAll 3 raw00325 (IntegerComputedClassCell.leftNumerator ![(49/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(49/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(49/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00325_transform
theorem leaf00325_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00325=true := by decide +kernel
#print axioms leaf00325_sign
theorem leaf00325_log : RationalLog.accepts (4731651/4294967296) (-7313175241/2147483648) 10 8=true := by decide +kernel
#print axioms leaf00325_log
def leaf00325 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (579100675737/1000000000000) (4731651/4294967296) (-7313175241/2147483648) 10 8 ![60,0,4] ![(49/6400),0,0] ![(1/6400),1,(1/16)] affine00325
theorem leaf00325_checked : FastNestedCellData.accepts 1 2 4 leaf00325=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (579100675737/1000000000000) (4731651/4294967296) (-7313175241/2147483648) 10 8 ![60,0,4] ![(49/6400),0,0] ![(1/6400),1,(1/16)] 3560840652744233825698960113664000000000000 6194627580111049421241950538444683870208 10696978676855066930114985984000000000000 raw00325 affine00325
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00325_raw leaf00325_rectangular
    leaf00325_transform leaf00325_sign leaf00325_log
#print axioms leaf00325_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
