/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00654 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1634494117197217585671515930624000000000000 1347546387857171518519997262215625075326976 15208279480918836146228674166784000000000000))
theorem leaf00654_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1634494117197217585671515930624000000000000 1347546387857171518519997262215625075326976 15208279480918836146228674166784000000000000 raw00654=true := by decide +kernel
#print axioms leaf00654_raw
theorem leaf00654_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00654=true := by decide +kernel
#print axioms leaf00654_rectangular
def affine00654 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00654 (IntegerComputedClassCell.leftNumerator ![(31/1280),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/1280),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/1280),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00654_transform : affine00654=(NestedInteger.clearedAll 3 raw00654 (IntegerComputedClassCell.leftNumerator ![(31/1280),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/1280),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/1280),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00654_transform
theorem leaf00654_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00654=true := by decide +kernel
#print axioms leaf00654_sign
theorem leaf00654_log : RationalLog.accepts (3252740811/4294967296) (-596884469/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00654_log
def leaf00654 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (88606103639/1000000000000) (3252740811/4294967296) (-596884469/4294967296) 1 8 ![60,0,4] ![(31/1280),0,(1/2)] ![(3/6400),1,(1/2)] affine00654
theorem leaf00654_checked : FastNestedCellData.accepts 1 2 4 leaf00654=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (88606103639/1000000000000) (3252740811/4294967296) (-596884469/4294967296) 1 8 ![60,0,4] ![(31/1280),0,(1/2)] ![(3/6400),1,(1/2)] 1634494117197217585671515930624000000000000 1347546387857171518519997262215625075326976 15208279480918836146228674166784000000000000 raw00654 affine00654
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00654_raw leaf00654_rectangular
    leaf00654_transform leaf00654_sign leaf00654_log
#print axioms leaf00654_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
