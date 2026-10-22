/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01026 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9576631415088637394022301696000000000000 6907616705377336651831950867850636296192 12993771472228119823849095168000000000000))
theorem leaf01026_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9576631415088637394022301696000000000000 6907616705377336651831950867850636296192 12993771472228119823849095168000000000000 raw01026=true := by decide +kernel
#print axioms leaf01026_raw
theorem leaf01026_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01026=true := by decide +kernel
#print axioms leaf01026_rectangular
def affine01026 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01026 (IntegerComputedClassCell.leftNumerator ![(1/5),0,(1/16)] ![(3/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/5),0,(1/16)] ![(3/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/5),0,(1/16)] ![(3/320),1,(1/16)]))
theorem leaf01026_transform : affine01026=(NestedInteger.clearedAll 3 raw01026 (IntegerComputedClassCell.leftNumerator ![(1/5),0,(1/16)] ![(3/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/5),0,(1/16)] ![(3/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/5),0,(1/16)] ![(3/320),1,(1/16)])) := by decide +kernel
#print axioms leaf01026_transform
theorem leaf01026_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01026=true := by decide +kernel
#print axioms leaf01026_sign
theorem leaf01026_log : RationalLog.accepts (63208749/134217728) (-202137435/536870912) 2 8=true := by decide +kernel
#print axioms leaf01026_log
def leaf01026 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (531609834769/1000000000000) (63208749/134217728) (-202137435/536870912) 2 8 ![60,0,4] ![(1/5),0,(1/16)] ![(3/320),1,(1/16)] affine01026
theorem leaf01026_checked : FastNestedCellData.accepts 1 2 4 leaf01026=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (531609834769/1000000000000) (63208749/134217728) (-202137435/536870912) 2 8 ![60,0,4] ![(1/5),0,(1/16)] ![(3/320),1,(1/16)] 9576631415088637394022301696000000000000 6907616705377336651831950867850636296192 12993771472228119823849095168000000000000 raw01026 affine01026
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01026_raw leaf01026_rectangular
    leaf01026_transform leaf01026_sign leaf01026_log
#print axioms leaf01026_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
