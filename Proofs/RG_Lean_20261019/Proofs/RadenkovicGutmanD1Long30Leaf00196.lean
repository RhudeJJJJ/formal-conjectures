/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00196 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 965860684635365547834427310080000000000 718792355297736521529294387756136398848 5491217866610636357929627811840000000000))
theorem leaf00196_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 965860684635365547834427310080000000000 718792355297736521529294387756136398848 5491217866610636357929627811840000000000 raw00196=true := by decide +kernel
#print axioms leaf00196_raw
theorem leaf00196_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00196=true := by decide +kernel
#print axioms leaf00196_rectangular
def affine00196 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00196 (IntegerComputedClassCell.leftNumerator ![(133/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(133/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(133/32000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00196_transform : affine00196=(NestedInteger.clearedAll 3 raw00196 (IntegerComputedClassCell.leftNumerator ![(133/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(133/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(133/32000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00196_transform
theorem leaf00196_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00196=true := by decide +kernel
#print axioms leaf00196_sign
theorem leaf00196_log : RationalLog.accepts (1413172529/2147483648) (-898635105/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00196_log
def leaf00196 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (5235941263/40000000000) (1413172529/2147483648) (-898635105/4294967296) 1 8 ![60,0,4] ![(133/32000),0,(1/16)] ![(3/32000),1,(1/16)] affine00196
theorem leaf00196_checked : FastNestedCellData.accepts 1 2 4 leaf00196=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (5235941263/40000000000) (1413172529/2147483648) (-898635105/4294967296) 1 8 ![60,0,4] ![(133/32000),0,(1/16)] ![(3/32000),1,(1/16)] 965860684635365547834427310080000000000 718792355297736521529294387756136398848 5491217866610636357929627811840000000000 raw00196 affine00196
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00196_raw leaf00196_rectangular
    leaf00196_transform leaf00196_sign leaf00196_log
#print axioms leaf00196_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
