/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00067 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 33066073165177421230153662464000000000000 30917574128563061715907450659323347206144 1078009351308026390871168516096000000000000))
theorem leaf00067_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 33066073165177421230153662464000000000000 30917574128563061715907450659323347206144 1078009351308026390871168516096000000000000 raw00067=true := by decide +kernel
#print axioms leaf00067_raw
theorem leaf00067_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00067=true := by decide +kernel
#print axioms leaf00067_rectangular
def affine00067 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00067 (IntegerComputedClassCell.leftNumerator ![(29/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(29/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(29/16000),0,(1/8)] ![(1/16000),1,(1/8)]))
theorem leaf00067_transform : affine00067=(NestedInteger.clearedAll 3 raw00067 (IntegerComputedClassCell.leftNumerator ![(29/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(29/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(29/16000),0,(1/8)] ![(1/16000),1,(1/8)])) := by decide +kernel
#print axioms leaf00067_transform
theorem leaf00067_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00067=true := by decide +kernel
#print axioms leaf00067_sign
theorem leaf00067_log : RationalLog.accepts (975983011/1073741824) (-25624767/536870912) 1 8=true := by decide +kernel
#print axioms leaf00067_log
def leaf00067 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (28680246689/1000000000000) (975983011/1073741824) (-25624767/536870912) 1 8 ![60,0,4] ![(29/16000),0,(1/8)] ![(1/16000),1,(1/8)] affine00067
theorem leaf00067_checked : FastNestedCellData.accepts 1 2 4 leaf00067=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (28680246689/1000000000000) (975983011/1073741824) (-25624767/536870912) 1 8 ![60,0,4] ![(29/16000),0,(1/8)] ![(1/16000),1,(1/8)] 33066073165177421230153662464000000000000 30917574128563061715907450659323347206144 1078009351308026390871168516096000000000000 raw00067 affine00067
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00067_raw leaf00067_rectangular
    leaf00067_transform leaf00067_sign leaf00067_log
#print axioms leaf00067_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
