/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00473 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 26608174951058955340678692864000000000000 21667705450389883684379379434166140534784 234713237709744540998711640064000000000000))
theorem leaf00473_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 26608174951058955340678692864000000000000 21667705450389883684379379434166140534784 234713237709744540998711640064000000000000 raw00473=true := by decide +kernel
#print axioms leaf00473_raw
theorem leaf00473_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00473=true := by decide +kernel
#print axioms leaf00473_rectangular
def affine00473 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00473 (IntegerComputedClassCell.leftNumerator ![(39/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(39/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(39/3200),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00473_transform : affine00473=(NestedInteger.clearedAll 3 raw00473 (IntegerComputedClassCell.leftNumerator ![(39/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(39/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(39/3200),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00473_transform
theorem leaf00473_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00473=true := by decide +kernel
#print axioms leaf00473_sign
theorem leaf00473_log : RationalLog.accepts (400239137/536870912) (-630706249/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00473_log
def leaf00473 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (92315651481/1000000000000) (400239137/536870912) (-630706249/4294967296) 1 8 ![60,0,4] ![(39/3200),0,(1/4)] ![(1/6400),1,(1/4)] affine00473
theorem leaf00473_checked : FastNestedCellData.accepts 1 2 4 leaf00473=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (92315651481/1000000000000) (400239137/536870912) (-630706249/4294967296) 1 8 ![60,0,4] ![(39/3200),0,(1/4)] ![(1/6400),1,(1/4)] 26608174951058955340678692864000000000000 21667705450389883684379379434166140534784 234713237709744540998711640064000000000000 raw00473 affine00473
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00473_raw leaf00473_rectangular
    leaf00473_transform leaf00473_sign leaf00473_log
#print axioms leaf00473_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
