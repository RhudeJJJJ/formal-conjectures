/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00171 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 45726637875430777645799833600000000000 35097769663986013630316688246677962752 300997340658024829606166528000000000000))
theorem leaf00171_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 45726637875430777645799833600000000000 35097769663986013630316688246677962752 300997340658024829606166528000000000000 raw00171=true := by decide +kernel
#print axioms leaf00171_raw
theorem leaf00171_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00171=true := by decide +kernel
#print axioms leaf00171_rectangular
def affine00171 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00171 (IntegerComputedClassCell.leftNumerator ![(59/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/16000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00171_transform : affine00171=(NestedInteger.clearedAll 3 raw00171 (IntegerComputedClassCell.leftNumerator ![(59/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/16000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00171_transform
theorem leaf00171_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00171=true := by decide +kernel
#print axioms leaf00171_sign
theorem leaf00171_log : RationalLog.accepts (738092145/1073741824) (-201238653/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00171_log
def leaf00171 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (58302458067/500000000000) (738092145/1073741824) (-201238653/1073741824) 1 8 ![60,0,4] ![(59/16000),0,(1/16)] ![(3/32000),1,(1/16)] affine00171
theorem leaf00171_checked : FastNestedCellData.accepts 1 2 4 leaf00171=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (58302458067/500000000000) (738092145/1073741824) (-201238653/1073741824) 1 8 ![60,0,4] ![(59/16000),0,(1/16)] ![(3/32000),1,(1/16)] 45726637875430777645799833600000000000 35097769663986013630316688246677962752 300997340658024829606166528000000000000 raw00171 affine00171
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00171_raw leaf00171_rectangular
    leaf00171_transform leaf00171_sign leaf00171_log
#print axioms leaf00171_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
