/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01093 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 182098101994570219379061319270400000000000 204241710821371655489372705813223425703936 827596669582152875499593505177600000000000))
theorem leaf01093_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 182098101994570219379061319270400000000000 204241710821371655489372705813223425703936 827596669582152875499593505177600000000000 raw01093=true := by decide +kernel
#print axioms leaf01093_raw
theorem leaf01093_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01093=true := by decide +kernel
#print axioms leaf01093_rectangular
def affine01093 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01093 (IntegerComputedClassCell.leftNumerator ![(37/80),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/80),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/80),0,(1/4)] ![(3/80),1,(1/4)]))
theorem leaf01093_transform : affine01093=(NestedInteger.clearedAll 3 raw01093 (IntegerComputedClassCell.leftNumerator ![(37/80),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/80),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/80),0,(1/4)] ![(3/80),1,(1/4)])) := by decide +kernel
#print axioms leaf01093_transform
theorem leaf01093_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01093=true := by decide +kernel
#print axioms leaf01093_sign
theorem leaf01093_log : RationalLog.accepts (3863722599/4294967296) (-227231333/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01093_log
def leaf01093 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (49357789447/200000000000) (3863722599/4294967296) (-227231333/4294967296) 1 8 ![60,0,4] ![(37/80),0,(1/4)] ![(3/80),1,(1/4)] affine01093
theorem leaf01093_checked : FastNestedCellData.accepts 1 2 4 leaf01093=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (49357789447/200000000000) (3863722599/4294967296) (-227231333/4294967296) 1 8 ![60,0,4] ![(37/80),0,(1/4)] ![(3/80),1,(1/4)] 182098101994570219379061319270400000000000 204241710821371655489372705813223425703936 827596669582152875499593505177600000000000 raw01093 affine01093
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01093_raw leaf01093_rectangular
    leaf01093_transform leaf01093_sign leaf01093_log
#print axioms leaf01093_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
