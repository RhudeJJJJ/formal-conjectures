/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01169 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1519958786120245173083858534400000000000 1928061667367433713420331518950675316736 33428030569021976769899737907200000000000))
theorem leaf01169_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1519958786120245173083858534400000000000 1928061667367433713420331518950675316736 33428030569021976769899737907200000000000 raw01169=true := by decide +kernel
#print axioms leaf01169_raw
theorem leaf01169_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01169=true := by decide +kernel
#print axioms leaf01169_rectangular
def affine01169 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01169 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(15/16)] ![(1/8),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(15/16)] ![(1/8),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/8),0,(15/16)] ![(1/8),1,(1/16)]))
theorem leaf01169_transform : affine01169=(NestedInteger.clearedAll 3 raw01169 (IntegerComputedClassCell.leftNumerator ![(5/8),0,(15/16)] ![(1/8),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/8),0,(15/16)] ![(1/8),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/8),0,(15/16)] ![(1/8),1,(1/16)])) := by decide +kernel
#print axioms leaf01169_transform
theorem leaf01169_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01169=true := by decide +kernel
#print axioms leaf01169_sign
theorem leaf01169_log : RationalLog.accepts (5151046873/4294967296) (97579525/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01169_log
def leaf01169 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (5767799163/100000000000) (5151046873/4294967296) (97579525/1073741824) 0 8 ![60,0,4] ![(5/8),0,(15/16)] ![(1/8),1,(1/16)] affine01169
theorem leaf01169_checked : FastNestedCellData.accepts 1 2 4 leaf01169=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (5767799163/100000000000) (5151046873/4294967296) (97579525/1073741824) 0 8 ![60,0,4] ![(5/8),0,(15/16)] ![(1/8),1,(1/16)] 1519958786120245173083858534400000000000 1928061667367433713420331518950675316736 33428030569021976769899737907200000000000 raw01169 affine01169
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01169_raw leaf01169_rectangular
    leaf01169_transform leaf01169_sign leaf01169_log
#print axioms leaf01169_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
