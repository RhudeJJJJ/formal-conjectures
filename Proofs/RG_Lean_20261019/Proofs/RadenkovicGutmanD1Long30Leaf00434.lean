/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00434 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 186849416682669936312263376896000000000000 170316197892768155014253003703199897485312 4203624728824963631258731020288000000000000))
theorem leaf00434_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 186849416682669936312263376896000000000000 170316197892768155014253003703199897485312 4203624728824963631258731020288000000000000 raw00434=true := by decide +kernel
#print axioms leaf00434_raw
theorem leaf00434_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00434=true := by decide +kernel
#print axioms leaf00434_rectangular
def affine00434 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00434 (IntegerComputedClassCell.leftNumerator ![(7/640),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/640),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/640),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00434_transform : affine00434=(NestedInteger.clearedAll 3 raw00434 (IntegerComputedClassCell.leftNumerator ![(7/640),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/640),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/640),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00434_transform
theorem leaf00434_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00434=true := by decide +kernel
#print axioms leaf00434_sign
theorem leaf00434_log : RationalLog.accepts (1881243869/2147483648) (-142124319/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00434_log
def leaf00434 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (40516508699/1000000000000) (1881243869/2147483648) (-142124319/2147483648) 1 8 ![60,0,4] ![(7/640),0,(1/2)] ![(1/6400),1,(1/2)] affine00434
theorem leaf00434_checked : FastNestedCellData.accepts 1 2 4 leaf00434=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (40516508699/1000000000000) (1881243869/2147483648) (-142124319/2147483648) 1 8 ![60,0,4] ![(7/640),0,(1/2)] ![(1/6400),1,(1/2)] 186849416682669936312263376896000000000000 170316197892768155014253003703199897485312 4203624728824963631258731020288000000000000 raw00434 affine00434
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00434_raw leaf00434_rectangular
    leaf00434_transform leaf00434_sign leaf00434_log
#print axioms leaf00434_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
