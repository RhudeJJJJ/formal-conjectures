/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00014 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 35107552849428461968116678656000000000000 34427589589798203269899852850282159407104 4522366860497750969583126183936000000000000))
theorem leaf00014_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 35107552849428461968116678656000000000000 34427589589798203269899852850282159407104 4522366860497750969583126183936000000000000 raw00014=true := by decide +kernel
#print axioms leaf00014_raw
theorem leaf00014_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00014=true := by decide +kernel
#print axioms leaf00014_rectangular
def affine00014 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00014 (IntegerComputedClassCell.leftNumerator ![(1/500),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/500),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/500),0,(1/2)] ![(3/16000),1,(1/2)]))
theorem leaf00014_transform : affine00014=(NestedInteger.clearedAll 3 raw00014 (IntegerComputedClassCell.leftNumerator ![(1/500),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/500),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/500),0,(1/2)] ![(3/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00014_transform
theorem leaf00014_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00014=true := by decide +kernel
#print axioms leaf00014_sign
theorem leaf00014_log : RationalLog.accepts (4179961401/4294967296) (-58286885/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00014_log
def leaf00014 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (3806368507/500000000000) (4179961401/4294967296) (-58286885/4294967296) 1 8 ![52,0,4] ![(1/500),0,(1/2)] ![(3/16000),1,(1/2)] affine00014
theorem leaf00014_checked : FastNestedCellData.accepts 1 0 4 leaf00014=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (3806368507/500000000000) (4179961401/4294967296) (-58286885/4294967296) 1 8 ![52,0,4] ![(1/500),0,(1/2)] ![(3/16000),1,(1/2)] 35107552849428461968116678656000000000000 34427589589798203269899852850282159407104 4522366860497750969583126183936000000000000 raw00014 affine00014
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00014_raw leaf00014_rectangular
    leaf00014_transform leaf00014_sign leaf00014_log
#print axioms leaf00014_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
