/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00279 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 419863328087996573886361632768000000000000 397989279195892499908896317365156067672064 17485705195639481916459443027968000000000000))
theorem leaf00279_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 419863328087996573886361632768000000000000 397989279195892499908896317365156067672064 17485705195639481916459443027968000000000000 raw00279=true := by decide +kernel
#print axioms leaf00279_raw
theorem leaf00279_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00279=true := by decide +kernel
#print axioms leaf00279_rectangular
def affine00279 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00279 (IntegerComputedClassCell.leftNumerator ![(39/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(39/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(39/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00279_transform : affine00279=(NestedInteger.clearedAll 3 raw00279 (IntegerComputedClassCell.leftNumerator ![(39/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(39/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(39/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00279_transform
theorem leaf00279_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00279=true := by decide +kernel
#print axioms leaf00279_sign
theorem leaf00279_log : RationalLog.accepts (3980606071/4294967296) (-163229955/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00279_log
def leaf00279 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (22760836623/1000000000000) (3980606071/4294967296) (-163229955/4294967296) 1 8 ![60,0,4] ![(39/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00279
theorem leaf00279_checked : FastNestedCellData.accepts 1 2 4 leaf00279=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (22760836623/1000000000000) (3980606071/4294967296) (-163229955/4294967296) 1 8 ![60,0,4] ![(39/6400),0,(1/2)] ![(1/6400),1,(1/2)] 419863328087996573886361632768000000000000 397989279195892499908896317365156067672064 17485705195639481916459443027968000000000000 raw00279 affine00279
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00279_raw leaf00279_rectangular
    leaf00279_transform leaf00279_sign leaf00279_log
#print axioms leaf00279_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
