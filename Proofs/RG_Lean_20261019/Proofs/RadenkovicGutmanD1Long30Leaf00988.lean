/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00988 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 178318492496227522063621947392000000000000 106587547335242791969682474602725736710144 229714584890293832559146041344000000000000))
theorem leaf00988_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 178318492496227522063621947392000000000000 106587547335242791969682474602725736710144 229714584890293832559146041344000000000000 raw00988=true := by decide +kernel
#print axioms leaf00988_raw
theorem leaf00988_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00988=true := by decide +kernel
#print axioms leaf00988_rectangular
def affine00988 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00988 (IntegerComputedClassCell.leftNumerator ![(21/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/160),0,(1/4)] ![(1/160),1,(1/4)]))
theorem leaf00988_transform : affine00988=(NestedInteger.clearedAll 3 raw00988 (IntegerComputedClassCell.leftNumerator ![(21/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/160),0,(1/4)] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00988_transform
theorem leaf00988_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00988=true := by decide +kernel
#print axioms leaf00988_sign
theorem leaf00988_log : RationalLog.accepts (438398343/1073741824) (-961833161/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00988_log
def leaf00988 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (463999912701/1000000000000) (438398343/1073741824) (-961833161/2147483648) 2 8 ![60,0,4] ![(21/160),0,(1/4)] ![(1/160),1,(1/4)] affine00988
theorem leaf00988_checked : FastNestedCellData.accepts 1 2 4 leaf00988=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (463999912701/1000000000000) (438398343/1073741824) (-961833161/2147483648) 2 8 ![60,0,4] ![(21/160),0,(1/4)] ![(1/160),1,(1/4)] 178318492496227522063621947392000000000000 106587547335242791969682474602725736710144 229714584890293832559146041344000000000000 raw00988 affine00988
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00988_raw leaf00988_rectangular
    leaf00988_transform leaf00988_sign leaf00988_log
#print axioms leaf00988_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
