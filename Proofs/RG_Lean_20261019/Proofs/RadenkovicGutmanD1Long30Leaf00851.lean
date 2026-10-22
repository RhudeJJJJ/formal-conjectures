/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00851 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 13295225199535118819608930287616000000000000 3419602339090824869816387178804679282786304 4744600278397139870910255202304000000000000))
theorem leaf00851_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 13295225199535118819608930287616000000000000 3419602339090824869816387178804679282786304 4744600278397139870910255202304000000000000 raw00851=true := by decide +kernel
#print axioms leaf00851_raw
theorem leaf00851_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00851=true := by decide +kernel
#print axioms leaf00851_rectangular
def affine00851 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00851 (IntegerComputedClassCell.leftNumerator ![(17/320),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/320),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/320),0,(1/16)] ![(1/640),1,(1/16)]))
theorem leaf00851_transform : affine00851=(NestedInteger.clearedAll 3 raw00851 (IntegerComputedClassCell.leftNumerator ![(17/320),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/320),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/320),0,(1/16)] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00851_transform
theorem leaf00851_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00851=true := by decide +kernel
#print axioms leaf00851_sign
theorem leaf00851_log : RationalLog.accepts (641986099/4294967296) (-4081577469/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00851_log
def leaf00851 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (720735602251/1000000000000) (641986099/4294967296) (-4081577469/4294967296) 3 8 ![60,0,4] ![(17/320),0,(1/16)] ![(1/640),1,(1/16)] affine00851
theorem leaf00851_checked : FastNestedCellData.accepts 1 2 4 leaf00851=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (720735602251/1000000000000) (641986099/4294967296) (-4081577469/4294967296) 3 8 ![60,0,4] ![(17/320),0,(1/16)] ![(1/640),1,(1/16)] 13295225199535118819608930287616000000000000 3419602339090824869816387178804679282786304 4744600278397139870910255202304000000000000 raw00851 affine00851
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00851_raw leaf00851_rectangular
    leaf00851_transform leaf00851_sign leaf00851_log
#print axioms leaf00851_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
