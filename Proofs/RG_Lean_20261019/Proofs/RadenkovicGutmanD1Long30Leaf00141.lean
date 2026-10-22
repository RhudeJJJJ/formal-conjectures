/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00141 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 91600405251288868561332941619200000000000 72999475023250814472482468313377554825216 735041853567625426966134390784000000000000))
theorem leaf00141_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 91600405251288868561332941619200000000000 72999475023250814472482468313377554825216 735041853567625426966134390784000000000000 raw00141=true := by decide +kernel
#print axioms leaf00141_raw
theorem leaf00141_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00141=true := by decide +kernel
#print axioms leaf00141_rectangular
def affine00141 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00141 (IntegerComputedClassCell.leftNumerator ![(1/320),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/320),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/320),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00141_transform : affine00141=(NestedInteger.clearedAll 3 raw00141 (IntegerComputedClassCell.leftNumerator ![(1/320),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/320),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/320),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00141_transform
theorem leaf00141_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00141=true := by decide +kernel
#print axioms leaf00141_sign
theorem leaf00141_log : RationalLog.accepts (3113584795/4294967296) (-690779407/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00141_log
def leaf00141 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (49656679187/500000000000) (3113584795/4294967296) (-690779407/4294967296) 1 8 ![60,0,4] ![(1/320),0,(1/16)] ![(3/32000),1,(1/16)] affine00141
theorem leaf00141_checked : FastNestedCellData.accepts 1 2 4 leaf00141=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (49656679187/500000000000) (3113584795/4294967296) (-690779407/4294967296) 1 8 ![60,0,4] ![(1/320),0,(1/16)] ![(3/32000),1,(1/16)] 91600405251288868561332941619200000000000 72999475023250814472482468313377554825216 735041853567625426966134390784000000000000 raw00141 affine00141
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00141_raw leaf00141_rectangular
    leaf00141_transform leaf00141_sign leaf00141_log
#print axioms leaf00141_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
