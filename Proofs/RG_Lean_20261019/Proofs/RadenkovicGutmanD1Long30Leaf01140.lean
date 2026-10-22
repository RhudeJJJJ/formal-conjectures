/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01140 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2006150436826467700190847434752000000000000 2560449852430147948917214952337064488599552 23543579920189155397308583510016000000000000))
theorem leaf01140_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2006150436826467700190847434752000000000000 2560449852430147948917214952337064488599552 23543579920189155397308583510016000000000000 raw01140=true := by decide +kernel
#print axioms leaf01140_raw
theorem leaf01140_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01140=true := by decide +kernel
#print axioms leaf01140_rectangular
def affine01140 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01140 (IntegerComputedClassCell.leftNumerator ![(15/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(15/16),0,0] ![(1/16),1,(1/2)]))
theorem leaf01140_transform : affine01140=(NestedInteger.clearedAll 3 raw01140 (IntegerComputedClassCell.leftNumerator ![(15/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(15/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(15/16),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf01140_transform
theorem leaf01140_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01140=true := by decide +kernel
#print axioms leaf01140_sign
theorem leaf01140_log : RationalLog.accepts (4943989993/4294967296) (75553175/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01140_log
def leaf01140 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (108753633097/1000000000000) (4943989993/4294967296) (75553175/1073741824) 0 8 ![60,0,4] ![(15/16),0,0] ![(1/16),1,(1/2)] affine01140
theorem leaf01140_checked : FastNestedCellData.accepts 1 2 4 leaf01140=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (108753633097/1000000000000) (4943989993/4294967296) (75553175/1073741824) 0 8 ![60,0,4] ![(15/16),0,0] ![(1/16),1,(1/2)] 2006150436826467700190847434752000000000000 2560449852430147948917214952337064488599552 23543579920189155397308583510016000000000000 raw01140 affine01140
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01140_raw leaf01140_rectangular
    leaf01140_transform leaf01140_sign leaf01140_log
#print axioms leaf01140_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
