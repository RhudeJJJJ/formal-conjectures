/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01137 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 109081369271634803136159914393600000000000 138193381587559401922555972788423443349504 1168493739970444780869110464512000000000000))
theorem leaf01137_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 109081369271634803136159914393600000000000 138193381587559401922555972788423443349504 1168493739970444780869110464512000000000000 raw01137=true := by decide +kernel
#print axioms leaf01137_raw
theorem leaf01137_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01137=true := by decide +kernel
#print axioms leaf01137_rectangular
def affine01137 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01137 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/8),0,(3/4)] ![(1/16),1,(1/8)]))
theorem leaf01137_transform : affine01137=(NestedInteger.clearedAll 3 raw01137 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/8),0,(3/4)] ![(1/16),1,(1/8)])) := by decide +kernel
#print axioms leaf01137_transform
theorem leaf01137_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01137=true := by decide +kernel
#print axioms leaf01137_sign
theorem leaf01137_log : RationalLog.accepts (4865766945/4294967296) (267963885/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01137_log
def leaf01137 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (59133128771/500000000000) (4865766945/4294967296) (267963885/4294967296) 0 8 ![60,0,4] ![(7/8),0,(3/4)] ![(1/16),1,(1/8)] affine01137
theorem leaf01137_checked : FastNestedCellData.accepts 1 2 4 leaf01137=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (59133128771/500000000000) (4865766945/4294967296) (267963885/4294967296) 0 8 ![60,0,4] ![(7/8),0,(3/4)] ![(1/16),1,(1/8)] 109081369271634803136159914393600000000000 138193381587559401922555972788423443349504 1168493739970444780869110464512000000000000 raw01137 affine01137
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01137_raw leaf01137_rectangular
    leaf01137_transform leaf01137_sign leaf01137_log
#print axioms leaf01137_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
