/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01054 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1862263686828200453700845568000000000 1672624198170037905694908660565671936 5177581512316527056791797760000000000))
theorem leaf01054_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1862263686828200453700845568000000000 1672624198170037905694908660565671936 5177581512316527056791797760000000000 raw01054=true := by decide +kernel
#print axioms leaf01054_raw
theorem leaf01054_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01054=true := by decide +kernel
#print axioms leaf01054_rectangular
def affine01054 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01054 (IntegerComputedClassCell.leftNumerator ![(11/40),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/40),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/40),0,(1/2)] ![(3/160),1,(1/2)]))
theorem leaf01054_transform : affine01054=(NestedInteger.clearedAll 3 raw01054 (IntegerComputedClassCell.leftNumerator ![(11/40),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/40),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/40),0,(1/2)] ![(3/160),1,(1/2)])) := by decide +kernel
#print axioms leaf01054_transform
theorem leaf01054_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01054=true := by decide +kernel
#print axioms leaf01054_sign
theorem leaf01054_log : RationalLog.accepts (2915683595/4294967296) (-831805577/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01054_log
def leaf01054 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (403814067/1250000000) (2915683595/4294967296) (-831805577/4294967296) 1 8 ![60,0,4] ![(11/40),0,(1/2)] ![(3/160),1,(1/2)] affine01054
theorem leaf01054_checked : FastNestedCellData.accepts 1 2 4 leaf01054=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (403814067/1250000000) (2915683595/4294967296) (-831805577/4294967296) 1 8 ![60,0,4] ![(11/40),0,(1/2)] ![(3/160),1,(1/2)] 1862263686828200453700845568000000000 1672624198170037905694908660565671936 5177581512316527056791797760000000000 raw01054 affine01054
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01054_raw leaf01054_rectangular
    leaf01054_transform leaf01054_sign leaf01054_log
#print axioms leaf01054_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
