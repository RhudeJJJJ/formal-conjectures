/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00227 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1361439707832475164247800676352000000000000 1150917389208861075207976739446701082804224 15594284790267228998532587323392000000000000))
theorem leaf00227_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1361439707832475164247800676352000000000000 1150917389208861075207976739446701082804224 15594284790267228998532587323392000000000000 raw00227=true := by decide +kernel
#print axioms leaf00227_raw
theorem leaf00227_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00227=true := by decide +kernel
#print axioms leaf00227_rectangular
def affine00227 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00227 (IntegerComputedClassCell.leftNumerator ![(151/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(151/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(151/32000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00227_transform : affine00227=(NestedInteger.clearedAll 3 raw00227 (IntegerComputedClassCell.leftNumerator ![(151/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(151/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(151/32000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00227_transform
theorem leaf00227_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00227=true := by decide +kernel
#print axioms leaf00227_sign
theorem leaf00227_log : RationalLog.accepts (3381276341/4294967296) (-513658125/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00227_log
def leaf00227 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (73803794447/1000000000000) (3381276341/4294967296) (-513658125/4294967296) 1 8 ![60,0,4] ![(151/32000),0,(1/8)] ![(3/32000),1,(1/8)] affine00227
theorem leaf00227_checked : FastNestedCellData.accepts 1 2 4 leaf00227=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (73803794447/1000000000000) (3381276341/4294967296) (-513658125/4294967296) 1 8 ![60,0,4] ![(151/32000),0,(1/8)] ![(3/32000),1,(1/8)] 1361439707832475164247800676352000000000000 1150917389208861075207976739446701082804224 15594284790267228998532587323392000000000000 raw00227 affine00227
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00227_raw leaf00227_rectangular
    leaf00227_transform leaf00227_sign leaf00227_log
#print axioms leaf00227_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
