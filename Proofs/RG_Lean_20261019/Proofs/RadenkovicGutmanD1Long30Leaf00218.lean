/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00218 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 17842628543763261090068168704000000000000 16459622997997926751310253236189770285056 472692020574796325934264745984000000000000))
theorem leaf00218_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 17842628543763261090068168704000000000000 16459622997997926751310253236189770285056 472692020574796325934264745984000000000000 raw00218=true := by decide +kernel
#print axioms leaf00218_raw
theorem leaf00218_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00218=true := by decide +kernel
#print axioms leaf00218_rectangular
def affine00218 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00218 (IntegerComputedClassCell.leftNumerator ![(29/6400),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/6400),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/6400),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00218_transform : affine00218=(NestedInteger.clearedAll 3 raw00218 (IntegerComputedClassCell.leftNumerator ![(29/6400),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/6400),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/6400),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00218_transform
theorem leaf00218_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00218=true := by decide +kernel
#print axioms leaf00218_sign
theorem leaf00218_log : RationalLog.accepts (3828738141/4294967296) (-123382251/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00218_log
def leaf00218 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (17410514967/500000000000) (3828738141/4294967296) (-123382251/2147483648) 1 8 ![60,0,4] ![(29/6400),0,(1/4)] ![(3/32000),1,(1/4)] affine00218
theorem leaf00218_checked : FastNestedCellData.accepts 1 2 4 leaf00218=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (17410514967/500000000000) (3828738141/4294967296) (-123382251/2147483648) 1 8 ![60,0,4] ![(29/6400),0,(1/4)] ![(3/32000),1,(1/4)] 17842628543763261090068168704000000000000 16459622997997926751310253236189770285056 472692020574796325934264745984000000000000 raw00218 affine00218
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00218_raw leaf00218_rectangular
    leaf00218_transform leaf00218_sign leaf00218_log
#print axioms leaf00218_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
