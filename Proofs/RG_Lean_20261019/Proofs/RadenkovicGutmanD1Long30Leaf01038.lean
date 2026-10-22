/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01038 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1923646258947967881232867393536000000000000 1516802182543049530450679498991880491761664 3636331464486337318257107664896000000000000))
theorem leaf01038_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1923646258947967881232867393536000000000000 1516802182543049530450679498991880491761664 3636331464486337318257107664896000000000000 raw01038=true := by decide +kernel
#print axioms leaf01038_raw
theorem leaf01038_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01038=true := by decide +kernel
#print axioms leaf01038_rectangular
def affine01038 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01038 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/32),0,(1/4)] ![(3/160),1,(1/4)]))
theorem leaf01038_transform : affine01038=(NestedInteger.clearedAll 3 raw01038 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/32),0,(1/4)] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf01038_transform
theorem leaf01038_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01038=true := by decide +kernel
#print axioms leaf01038_sign
theorem leaf01038_log : RationalLog.accepts (1194883753/2147483648) (-314739431/1073741824) 1 8=true := by decide +kernel
#print axioms leaf01038_log
def leaf01038 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (417124290609/1000000000000) (1194883753/2147483648) (-314739431/1073741824) 1 8 ![60,0,4] ![(7/32),0,(1/4)] ![(3/160),1,(1/4)] affine01038
theorem leaf01038_checked : FastNestedCellData.accepts 1 2 4 leaf01038=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (417124290609/1000000000000) (1194883753/2147483648) (-314739431/1073741824) 1 8 ![60,0,4] ![(7/32),0,(1/4)] ![(3/160),1,(1/4)] 1923646258947967881232867393536000000000000 1516802182543049530450679498991880491761664 3636331464486337318257107664896000000000000 raw01038 affine01038
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01038_raw leaf01038_rectangular
    leaf01038_transform leaf01038_sign leaf01038_log
#print axioms leaf01038_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
