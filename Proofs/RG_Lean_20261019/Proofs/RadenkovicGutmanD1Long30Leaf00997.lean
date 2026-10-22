/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00997 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 651824046460945971293009739776000000000000 372596511549574360680338077572645796184064 659034494108274142704895524864000000000000))
theorem leaf00997_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 651824046460945971293009739776000000000000 372596511549574360680338077572645796184064 659034494108274142704895524864000000000000 raw00997=true := by decide +kernel
#print axioms leaf00997_raw
theorem leaf00997_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00997=true := by decide +kernel
#print axioms leaf00997_rectangular
def affine00997 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00997 (IntegerComputedClassCell.leftNumerator ![(23/160),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/160),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/160),0,(1/8)] ![(1/160),1,(1/8)]))
theorem leaf00997_transform : affine00997=(NestedInteger.clearedAll 3 raw00997 (IntegerComputedClassCell.leftNumerator ![(23/160),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/160),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/160),0,(1/8)] ![(1/160),1,(1/8)])) := by decide +kernel
#print axioms leaf00997_transform
theorem leaf00997_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00997=true := by decide +kernel
#print axioms leaf00997_sign
theorem leaf00997_log : RationalLog.accepts (392095661/1073741824) (-270421623/536870912) 2 8=true := by decide +kernel
#print axioms leaf00997_log
def leaf00997 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (565367237801/1000000000000) (392095661/1073741824) (-270421623/536870912) 2 8 ![60,0,4] ![(23/160),0,(1/8)] ![(1/160),1,(1/8)] affine00997
theorem leaf00997_checked : FastNestedCellData.accepts 1 2 4 leaf00997=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (565367237801/1000000000000) (392095661/1073741824) (-270421623/536870912) 2 8 ![60,0,4] ![(23/160),0,(1/8)] ![(1/160),1,(1/8)] 651824046460945971293009739776000000000000 372596511549574360680338077572645796184064 659034494108274142704895524864000000000000 raw00997 affine00997
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00997_raw leaf00997_rectangular
    leaf00997_transform leaf00997_sign leaf00997_log
#print axioms leaf00997_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
