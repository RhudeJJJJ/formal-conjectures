/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00164 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 201237155335913188704963788800000000000 195078915453248456680271428105751494656 14901865502653729816907979161600000000000))
theorem leaf00164_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 201237155335913188704963788800000000000 195078915453248456680271428105751494656 14901865502653729816907979161600000000000 raw00164=true := by decide +kernel
#print axioms leaf00164_raw
theorem leaf00164_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00164=true := by decide +kernel
#print axioms leaf00164_rectangular
def affine00164 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00164 (IntegerComputedClassCell.leftNumerator ![(7/2000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/2000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/2000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00164_transform : affine00164=(NestedInteger.clearedAll 3 raw00164 (IntegerComputedClassCell.leftNumerator ![(7/2000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/2000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/2000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00164_transform
theorem leaf00164_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00164=true := by decide +kernel
#print axioms leaf00164_sign
theorem leaf00164_log : RationalLog.accepts (4109732997/4294967296) (-23668435/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00164_log
def leaf00164 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (654545283/50000000000) (4109732997/4294967296) (-23668435/1073741824) 1 8 ![60,0,4] ![(7/2000),0,(1/2)] ![(3/32000),1,(1/2)] affine00164
theorem leaf00164_checked : FastNestedCellData.accepts 1 2 4 leaf00164=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (654545283/50000000000) (4109732997/4294967296) (-23668435/1073741824) 1 8 ![60,0,4] ![(7/2000),0,(1/2)] ![(3/32000),1,(1/2)] 201237155335913188704963788800000000000 195078915453248456680271428105751494656 14901865502653729816907979161600000000000 raw00164 affine00164
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00164_raw leaf00164_rectangular
    leaf00164_transform leaf00164_sign leaf00164_log
#print axioms leaf00164_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
