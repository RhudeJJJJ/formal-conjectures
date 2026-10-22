/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00905 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 38971246348489409869040215654400000000000 6505489378928498034339904724688596631552 7698310221734882959795893043200000000000))
theorem leaf00905_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 38971246348489409869040215654400000000000 6505489378928498034339904724688596631552 7698310221734882959795893043200000000000 raw00905=true := by decide +kernel
#print axioms leaf00905_raw
theorem leaf00905_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00905=true := by decide +kernel
#print axioms leaf00905_rectangular
def affine00905 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00905 (IntegerComputedClassCell.leftNumerator ![(9/128),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/128),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/128),0,0] ![(1/640),1,(1/16)]))
theorem leaf00905_transform : affine00905=(NestedInteger.clearedAll 3 raw00905 (IntegerComputedClassCell.leftNumerator ![(9/128),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/128),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/128),0,0] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00905_transform
theorem leaf00905_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00905=true := by decide +kernel
#print axioms leaf00905_sign
theorem leaf00905_log : RationalLog.accepts (194292669/2147483648) (-5159729927/4294967296) 4 8=true := by decide +kernel
#print axioms leaf00905_log
def leaf00905 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (84505419911/100000000000) (194292669/2147483648) (-5159729927/4294967296) 4 8 ![60,0,4] ![(9/128),0,0] ![(1/640),1,(1/16)] affine00905
theorem leaf00905_checked : FastNestedCellData.accepts 1 2 4 leaf00905=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (84505419911/100000000000) (194292669/2147483648) (-5159729927/4294967296) 4 8 ![60,0,4] ![(9/128),0,0] ![(1/640),1,(1/16)] 38971246348489409869040215654400000000000 6505489378928498034339904724688596631552 7698310221734882959795893043200000000000 raw00905 affine00905
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00905_raw leaf00905_rectangular
    leaf00905_transform leaf00905_sign leaf00905_log
#print axioms leaf00905_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
