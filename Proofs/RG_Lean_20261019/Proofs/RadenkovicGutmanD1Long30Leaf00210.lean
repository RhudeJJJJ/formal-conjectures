/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00210 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 17952821488199182065957915852800000000000 8021836757462379916608045761968472064 20606338920494093927920435200000000000))
theorem leaf00210_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 17952821488199182065957915852800000000000 8021836757462379916608045761968472064 20606338920494093927920435200000000000 raw00210=true := by decide +kernel
#print axioms leaf00210_raw
theorem leaf00210_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00210=true := by decide +kernel
#print axioms leaf00210_rectangular
def affine00210 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00210 (IntegerComputedClassCell.leftNumerator ![(71/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(71/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(71/16000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00210_transform : affine00210=(NestedInteger.clearedAll 3 raw00210 (IntegerComputedClassCell.leftNumerator ![(71/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(71/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(71/16000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00210_transform
theorem leaf00210_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00210=true := by decide +kernel
#print axioms leaf00210_sign
theorem leaf00210_log : RationalLog.accepts (345341/1073741824) (-2158792297/536870912) 12 8=true := by decide +kernel
#print axioms leaf00210_log
def leaf00210 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (77857952239/200000000000) (345341/1073741824) (-2158792297/536870912) 12 8 ![60,0,4] ![(71/16000),0,0] ![(3/32000),1,(1/16)] affine00210
theorem leaf00210_checked : FastNestedCellData.accepts 1 2 4 leaf00210=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (77857952239/200000000000) (345341/1073741824) (-2158792297/536870912) 12 8 ![60,0,4] ![(71/16000),0,0] ![(3/32000),1,(1/16)] 17952821488199182065957915852800000000000 8021836757462379916608045761968472064 20606338920494093927920435200000000000 raw00210 affine00210
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00210_raw leaf00210_rectangular
    leaf00210_transform leaf00210_sign leaf00210_log
#print axioms leaf00210_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
