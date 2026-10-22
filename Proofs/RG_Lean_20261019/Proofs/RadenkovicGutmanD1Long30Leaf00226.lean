/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00226 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 170510115689444111157573976064000000000000 122334712520160414924258425925576595341312 827178611979095805219211051008000000000000))
theorem leaf00226_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 170510115689444111157573976064000000000000 122334712520160414924258425925576595341312 827178611979095805219211051008000000000000 raw00226=true := by decide +kernel
#print axioms leaf00226_raw
theorem leaf00226_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00226=true := by decide +kernel
#print axioms leaf00226_rectangular
def affine00226 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00226 (IntegerComputedClassCell.leftNumerator ![(151/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(151/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(151/32000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00226_transform : affine00226=(NestedInteger.clearedAll 3 raw00226 (IntegerComputedClassCell.leftNumerator ![(151/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(151/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(151/32000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00226_transform
theorem leaf00226_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00226=true := by decide +kernel
#print axioms leaf00226_sign
theorem leaf00226_log : RationalLog.accepts (671116103/1073741824) (-63077329/268435456) 1 8=true := by decide +kernel
#print axioms leaf00226_log
def leaf00226 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (147893950289/1000000000000) (671116103/1073741824) (-63077329/268435456) 1 8 ![60,0,4] ![(151/32000),0,(1/16)] ![(3/32000),1,(1/16)] affine00226
theorem leaf00226_checked : FastNestedCellData.accepts 1 2 4 leaf00226=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (147893950289/1000000000000) (671116103/1073741824) (-63077329/268435456) 1 8 ![60,0,4] ![(151/32000),0,(1/16)] ![(3/32000),1,(1/16)] 170510115689444111157573976064000000000000 122334712520160414924258425925576595341312 827178611979095805219211051008000000000000 raw00226 affine00226
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00226_raw leaf00226_rectangular
    leaf00226_transform leaf00226_sign leaf00226_log
#print axioms leaf00226_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
