/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01127 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2570486936247363646577967104000000000000 3193869620321698469703666569297560338432 22383167685652152673445609472000000000000))
theorem leaf01127_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2570486936247363646577967104000000000000 3193869620321698469703666569297560338432 22383167685652152673445609472000000000000 raw01127=true := by decide +kernel
#print axioms leaf01127_raw
theorem leaf01127_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01127=true := by decide +kernel
#print axioms leaf01127_rectangular
def affine01127 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01127 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/4),0,(3/4)] ![(1/16),1,(1/8)]))
theorem leaf01127_transform : affine01127=(NestedInteger.clearedAll 3 raw01127 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/4),0,(3/4)] ![(1/16),1,(1/8)])) := by decide +kernel
#print axioms leaf01127_transform
theorem leaf01127_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01127=true := by decide +kernel
#print axioms leaf01127_sign
theorem leaf01127_log : RationalLog.accepts (4670172853/4294967296) (89928179/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01127_log
def leaf01127 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4459084033/31250000000) (4670172853/4294967296) (89928179/2147483648) 0 8 ![60,0,4] ![(3/4),0,(3/4)] ![(1/16),1,(1/8)] affine01127
theorem leaf01127_checked : FastNestedCellData.accepts 1 2 4 leaf01127=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4459084033/31250000000) (4670172853/4294967296) (89928179/2147483648) 0 8 ![60,0,4] ![(3/4),0,(3/4)] ![(1/16),1,(1/8)] 2570486936247363646577967104000000000000 3193869620321698469703666569297560338432 22383167685652152673445609472000000000000 raw01127 affine01127
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01127_raw leaf01127_rectangular
    leaf01127_transform leaf01127_sign leaf01127_log
#print axioms leaf01127_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
