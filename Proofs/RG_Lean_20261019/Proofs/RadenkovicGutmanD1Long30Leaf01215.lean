/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01215 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 675162049755795758699144806400000000000 765238870675368416765834250621265379328 65336932850550565431857381376000000000000))
theorem leaf01215_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 675162049755795758699144806400000000000 765238870675368416765834250621265379328 65336932850550565431857381376000000000000 raw01215=true := by decide +kernel
#print axioms leaf01215_raw
theorem leaf01215_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01215=true := by decide +kernel
#print axioms leaf01215_rectangular
def affine01215 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01215 (IntegerComputedClassCell.leftNumerator ![(5/16),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/16),0,0] ![(1/64),1,(1/2)]))
theorem leaf01215_transform : affine01215=(NestedInteger.clearedAll 3 raw01215 (IntegerComputedClassCell.leftNumerator ![(5/16),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(5/16),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf01215_transform
theorem leaf01215_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01215=true := by decide +kernel
#print axioms leaf01215_sign
theorem leaf01215_log : RationalLog.accepts (1202906535/1073741824) (30491895/536870912) 0 8=true := by decide +kernel
#print axioms leaf01215_log
def leaf01215 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (5856097289/500000000000) (1202906535/1073741824) (30491895/536870912) 0 8 ![60,0,4] ![(5/16),0,0] ![(1/64),1,(1/2)] affine01215
theorem leaf01215_checked : FastNestedCellData.accepts 1 2 4 leaf01215=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (5856097289/500000000000) (1202906535/1073741824) (30491895/536870912) 0 8 ![60,0,4] ![(5/16),0,0] ![(1/64),1,(1/2)] 675162049755795758699144806400000000000 765238870675368416765834250621265379328 65336932850550565431857381376000000000000 raw01215 affine01215
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01215_raw leaf01215_rectangular
    leaf01215_transform leaf01215_sign leaf01215_log
#print axioms leaf01215_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
