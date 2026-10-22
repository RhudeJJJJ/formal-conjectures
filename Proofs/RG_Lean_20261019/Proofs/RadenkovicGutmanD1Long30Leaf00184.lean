/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00184 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3337402227487583764486710886400000000000 3225076134356596510364284022107184037888 222823584084029869668679286784000000000000))
theorem leaf00184_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3337402227487583764486710886400000000000 3225076134356596510364284022107184037888 222823584084029869668679286784000000000000 raw00184=true := by decide +kernel
#print axioms leaf00184_raw
theorem leaf00184_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00184=true := by decide +kernel
#print axioms leaf00184_rectangular
def affine00184 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00184 (IntegerComputedClassCell.leftNumerator ![(31/8000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/8000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/8000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00184_transform : affine00184=(NestedInteger.clearedAll 3 raw00184 (IntegerComputedClassCell.leftNumerator ![(31/8000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/8000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/8000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00184_transform
theorem leaf00184_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00184=true := by decide +kernel
#print axioms leaf00184_sign
theorem leaf00184_log : RationalLog.accepts (2045599005/2147483648) (-104380845/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00184_log
def leaf00184 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (7236837491/500000000000) (2045599005/2147483648) (-104380845/4294967296) 1 8 ![60,0,4] ![(31/8000),0,(1/2)] ![(3/32000),1,(1/2)] affine00184
theorem leaf00184_checked : FastNestedCellData.accepts 1 2 4 leaf00184=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (7236837491/500000000000) (2045599005/2147483648) (-104380845/4294967296) 1 8 ![60,0,4] ![(31/8000),0,(1/2)] ![(3/32000),1,(1/2)] 3337402227487583764486710886400000000000 3225076134356596510364284022107184037888 222823584084029869668679286784000000000000 raw00184 affine00184
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00184_raw leaf00184_rectangular
    leaf00184_transform leaf00184_sign leaf00184_log
#print axioms leaf00184_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
