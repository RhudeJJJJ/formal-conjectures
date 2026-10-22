/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00185 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 16360770571355001255087413657600000000000 5465125798979488307632762266316701696 15404802681010373010024038400000000000))
theorem leaf00185_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 16360770571355001255087413657600000000000 5465125798979488307632762266316701696 15404802681010373010024038400000000000 raw00185=true := by decide +kernel
#print axioms leaf00185_raw
theorem leaf00185_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00185=true := by decide +kernel
#print axioms leaf00185_rectangular
def affine00185 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00185 (IntegerComputedClassCell.leftNumerator ![(127/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(127/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(127/32000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00185_transform : affine00185=(NestedInteger.clearedAll 3 raw00185 (IntegerComputedClassCell.leftNumerator ![(127/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(127/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(127/32000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00185_transform
theorem leaf00185_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00185=true := by decide +kernel
#print axioms leaf00185_sign
theorem leaf00185_log : RationalLog.accepts (1058989/4294967296) (-557532707/134217728) 12 8=true := by decide +kernel
#print axioms leaf00185_log
def leaf00185 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (17738382997/50000000000) (1058989/4294967296) (-557532707/134217728) 12 8 ![60,0,4] ![(127/32000),0,0] ![(3/32000),1,(1/16)] affine00185
theorem leaf00185_checked : FastNestedCellData.accepts 1 2 4 leaf00185=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (17738382997/50000000000) (1058989/4294967296) (-557532707/134217728) 12 8 ![60,0,4] ![(127/32000),0,0] ![(3/32000),1,(1/16)] 16360770571355001255087413657600000000000 5465125798979488307632762266316701696 15404802681010373010024038400000000000 raw00185 affine00185
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00185_raw leaf00185_rectangular
    leaf00185_transform leaf00185_sign leaf00185_log
#print axioms leaf00185_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
