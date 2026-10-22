/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00663 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3391657600012016205921316241408000000000000 2305841326225117920512837104954168414568448 12541143545653626692704923549696000000000000))
theorem leaf00663_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3391657600012016205921316241408000000000000 2305841326225117920512837104954168414568448 12541143545653626692704923549696000000000000 raw00663=true := by decide +kernel
#print axioms leaf00663_raw
theorem leaf00663_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00663=true := by decide +kernel
#print axioms leaf00663_rectangular
def affine00663 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00663 (IntegerComputedClassCell.leftNumerator ![(161/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(161/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(161/6400),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00663_transform : affine00663=(NestedInteger.clearedAll 3 raw00663 (IntegerComputedClassCell.leftNumerator ![(161/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(161/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(161/6400),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00663_transform
theorem leaf00663_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00663=true := by decide +kernel
#print axioms leaf00663_sign
theorem leaf00663_log : RationalLog.accepts (2466471777/4294967296) (-595556549/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00663_log
def leaf00663 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (183862126913/1000000000000) (2466471777/4294967296) (-595556549/2147483648) 1 8 ![60,0,4] ![(161/6400),0,(1/4)] ![(3/6400),1,(1/4)] affine00663
theorem leaf00663_checked : FastNestedCellData.accepts 1 2 4 leaf00663=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (183862126913/1000000000000) (2466471777/4294967296) (-595556549/2147483648) 1 8 ![60,0,4] ![(161/6400),0,(1/4)] ![(3/6400),1,(1/4)] 3391657600012016205921316241408000000000000 2305841326225117920512837104954168414568448 12541143545653626692704923549696000000000000 raw00663 affine00663
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00663_raw leaf00663_rectangular
    leaf00663_transform leaf00663_sign leaf00663_log
#print axioms leaf00663_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
