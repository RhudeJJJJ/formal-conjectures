/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01190 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 102230322704395693681568382976000000000000 121213951621017589541218985708106559782912 5468051661593207014290408603648000000000000))
theorem leaf01190_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 102230322704395693681568382976000000000000 121213951621017589541218985708106559782912 5468051661593207014290408603648000000000000 raw01190=true := by decide +kernel
#print axioms leaf01190_raw
theorem leaf01190_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01190=true := by decide +kernel
#print axioms leaf01190_rectangular
def affine01190 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01190 (IntegerComputedClassCell.leftNumerator ![(13/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/32),0,0] ![(1/32),1,(1/2)]))
theorem leaf01190_transform : affine01190=(NestedInteger.clearedAll 3 raw01190 (IntegerComputedClassCell.leftNumerator ![(13/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/32),0,0] ![(1/32),1,(1/2)])) := by decide +kernel
#print axioms leaf01190_transform
theorem leaf01190_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01190=true := by decide +kernel
#print axioms leaf01190_sign
theorem leaf01190_log : RationalLog.accepts (4982078883/4294967296) (19918355/268435456) 0 8=true := by decide +kernel
#print axioms leaf01190_log
def leaf01190 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (11083833797/500000000000) (4982078883/4294967296) (19918355/268435456) 0 8 ![60,0,4] ![(13/32),0,0] ![(1/32),1,(1/2)] affine01190
theorem leaf01190_checked : FastNestedCellData.accepts 1 2 4 leaf01190=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (11083833797/500000000000) (4982078883/4294967296) (19918355/268435456) 0 8 ![60,0,4] ![(13/32),0,0] ![(1/32),1,(1/2)] 102230322704395693681568382976000000000000 121213951621017589541218985708106559782912 5468051661593207014290408603648000000000000 raw01190 affine01190
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01190_raw leaf01190_rectangular
    leaf01190_transform leaf01190_sign leaf01190_log
#print axioms leaf01190_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
