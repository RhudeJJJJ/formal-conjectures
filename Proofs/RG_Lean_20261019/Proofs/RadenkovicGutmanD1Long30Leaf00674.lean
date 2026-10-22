/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00674 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 438659595764975852894885511168000000000000 357226211470098743756327436432810392420352 3755566140026008897320340422656000000000000))
theorem leaf00674_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 438659595764975852894885511168000000000000 357226211470098743756327436432810392420352 3755566140026008897320340422656000000000000 raw00674=true := by decide +kernel
#print axioms leaf00674_raw
theorem leaf00674_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00674=true := by decide +kernel
#print axioms leaf00674_rectangular
def affine00674 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00674 (IntegerComputedClassCell.leftNumerator ![(167/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(167/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(167/6400),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00674_transform : affine00674=(NestedInteger.clearedAll 3 raw00674 (IntegerComputedClassCell.leftNumerator ![(167/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(167/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(167/6400),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00674_transform
theorem leaf00674_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00674=true := by decide +kernel
#print axioms leaf00674_sign
theorem leaf00674_log : RationalLog.accepts (3193847507/4294967296) (-636122565/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00674_log
def leaf00674 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (47559568671/500000000000) (3193847507/4294967296) (-636122565/4294967296) 1 8 ![60,0,4] ![(167/6400),0,(1/2)] ![(3/6400),1,(1/2)] affine00674
theorem leaf00674_checked : FastNestedCellData.accepts 1 2 4 leaf00674=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (47559568671/500000000000) (3193847507/4294967296) (-636122565/4294967296) 1 8 ![60,0,4] ![(167/6400),0,(1/2)] ![(3/6400),1,(1/2)] 438659595764975852894885511168000000000000 357226211470098743756327436432810392420352 3755566140026008897320340422656000000000000 raw00674 affine00674
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00674_raw leaf00674_rectangular
    leaf00674_transform leaf00674_sign leaf00674_log
#print axioms leaf00674_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
