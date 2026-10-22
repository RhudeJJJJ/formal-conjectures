/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00862 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 126521821095902669764474123059200000000000 48316803044142086586578218526534518439936 88056717459386878725315362816000000000000))
theorem leaf00862_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 126521821095902669764474123059200000000000 48316803044142086586578218526534518439936 88056717459386878725315362816000000000000 raw00862=true := by decide +kernel
#print axioms leaf00862_raw
theorem leaf00862_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00862=true := by decide +kernel
#print axioms leaf00862_rectangular
def affine00862 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00862 (IntegerComputedClassCell.leftNumerator ![(9/160),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/160),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/160),0,(1/8)] ![(1/640),1,(1/8)]))
theorem leaf00862_transform : affine00862=(NestedInteger.clearedAll 3 raw00862 (IntegerComputedClassCell.leftNumerator ![(9/160),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/160),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/160),0,(1/8)] ![(1/640),1,(1/8)])) := by decide +kernel
#print axioms leaf00862_transform
theorem leaf00862_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00862=true := by decide +kernel
#print axioms leaf00862_sign
theorem leaf00862_log : RationalLog.accepts (1059070955/4294967296) (-3006588615/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00862_log
def leaf00862 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (137175233299/250000000000) (1059070955/4294967296) (-3006588615/4294967296) 3 8 ![60,0,4] ![(9/160),0,(1/8)] ![(1/640),1,(1/8)] affine00862
theorem leaf00862_checked : FastNestedCellData.accepts 1 2 4 leaf00862=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (137175233299/250000000000) (1059070955/4294967296) (-3006588615/4294967296) 3 8 ![60,0,4] ![(9/160),0,(1/8)] ![(1/640),1,(1/8)] 126521821095902669764474123059200000000000 48316803044142086586578218526534518439936 88056717459386878725315362816000000000000 raw00862 affine00862
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00862_raw leaf00862_rectangular
    leaf00862_transform leaf00862_sign leaf00862_log
#print axioms leaf00862_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
