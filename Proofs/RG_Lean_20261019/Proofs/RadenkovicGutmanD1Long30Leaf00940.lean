/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00940 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 225893921586430671499296768000000000000 57667913110378555307089123102842421248 71857066297754643979042816000000000000))
theorem leaf00940_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 225893921586430671499296768000000000000 57667913110378555307089123102842421248 71857066297754643979042816000000000000 raw00940=true := by decide +kernel
#print axioms leaf00940_raw
theorem leaf00940_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00940=true := by decide +kernel
#print axioms leaf00940_rectangular
def affine00940 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00940 (IntegerComputedClassCell.leftNumerator ![(29/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/320),0,0] ![(1/320),1,(1/16)]))
theorem leaf00940_transform : affine00940=(NestedInteger.clearedAll 3 raw00940 (IntegerComputedClassCell.leftNumerator ![(29/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/320),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/320),0,0] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00940_transform
theorem leaf00940_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00940=true := by decide +kernel
#print axioms leaf00940_sign
theorem leaf00940_log : RationalLog.accepts (4752209/33554432) (-4197384443/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00940_log
def leaf00940 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (401268212589/500000000000) (4752209/33554432) (-4197384443/4294967296) 3 8 ![60,0,4] ![(29/320),0,0] ![(1/320),1,(1/16)] affine00940
theorem leaf00940_checked : FastNestedCellData.accepts 1 2 4 leaf00940=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (401268212589/500000000000) (4752209/33554432) (-4197384443/4294967296) 3 8 ![60,0,4] ![(29/320),0,0] ![(1/320),1,(1/16)] 225893921586430671499296768000000000000 57667913110378555307089123102842421248 71857066297754643979042816000000000000 raw00940 affine00940
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00940_raw leaf00940_rectangular
    leaf00940_transform leaf00940_sign leaf00940_log
#print axioms leaf00940_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
