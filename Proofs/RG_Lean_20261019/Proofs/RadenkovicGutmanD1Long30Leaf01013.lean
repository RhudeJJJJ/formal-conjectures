/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01013 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 105128599209455926954937653657600000000000 69869700322494453466950720894978043674624 153249031430058755014627688448000000000000))
theorem leaf01013_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 105128599209455926954937653657600000000000 69869700322494453466950720894978043674624 153249031430058755014627688448000000000000 raw01013=true := by decide +kernel
#print axioms leaf01013_raw
theorem leaf01013_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01013=true := by decide +kernel
#print axioms leaf01013_rectangular
def affine01013 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01013 (IntegerComputedClassCell.leftNumerator ![(13/80),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/80),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/80),0,(1/4)] ![(1/80),1,(1/4)]))
theorem leaf01013_transform : affine01013=(NestedInteger.clearedAll 3 raw01013 (IntegerComputedClassCell.leftNumerator ![(13/80),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/80),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/80),0,(1/4)] ![(1/80),1,(1/4)])) := by decide +kernel
#print axioms leaf01013_transform
theorem leaf01013_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01013=true := by decide +kernel
#print axioms leaf01013_sign
theorem leaf01013_log : RationalLog.accepts (490150645/1073741824) (-421009933/1073741824) 2 8=true := by decide +kernel
#print axioms leaf01013_log
def leaf01013 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (455922622613/1000000000000) (490150645/1073741824) (-421009933/1073741824) 2 8 ![60,0,4] ![(13/80),0,(1/4)] ![(1/80),1,(1/4)] affine01013
theorem leaf01013_checked : FastNestedCellData.accepts 1 2 4 leaf01013=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (455922622613/1000000000000) (490150645/1073741824) (-421009933/1073741824) 2 8 ![60,0,4] ![(13/80),0,(1/4)] ![(1/80),1,(1/4)] 105128599209455926954937653657600000000000 69869700322494453466950720894978043674624 153249031430058755014627688448000000000000 raw01013 affine01013
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01013_raw leaf01013_rectangular
    leaf01013_transform leaf01013_sign leaf01013_log
#print axioms leaf01013_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
