/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00438 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 44408053089972682068358646988800000000000 36775200387510600514883747205404891807744 436460546876395829412849778688000000000000))
theorem leaf00438_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 44408053089972682068358646988800000000000 36775200387510600514883747205404891807744 436460546876395829412849778688000000000000 raw00438=true := by decide +kernel
#print axioms leaf00438_raw
theorem leaf00438_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00438=true := by decide +kernel
#print axioms leaf00438_rectangular
def affine00438 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00438 (IntegerComputedClassCell.leftNumerator ![(71/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(71/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(71/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00438_transform : affine00438=(NestedInteger.clearedAll 3 raw00438 (IntegerComputedClassCell.leftNumerator ![(71/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(71/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(71/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00438_transform
theorem leaf00438_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00438=true := by decide +kernel
#print axioms leaf00438_sign
theorem leaf00438_log : RationalLog.accepts (3280353335/4294967296) (-289365709/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00438_log
def leaf00438 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (84257788363/1000000000000) (3280353335/4294967296) (-289365709/2147483648) 1 8 ![60,0,4] ![(71/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00438
theorem leaf00438_checked : FastNestedCellData.accepts 1 2 4 leaf00438=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (84257788363/1000000000000) (3280353335/4294967296) (-289365709/2147483648) 1 8 ![60,0,4] ![(71/6400),0,(1/4)] ![(1/6400),1,(1/4)] 44408053089972682068358646988800000000000 36775200387510600514883747205404891807744 436460546876395829412849778688000000000000 raw00438 affine00438
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00438_raw leaf00438_rectangular
    leaf00438_transform leaf00438_sign leaf00438_log
#print axioms leaf00438_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
