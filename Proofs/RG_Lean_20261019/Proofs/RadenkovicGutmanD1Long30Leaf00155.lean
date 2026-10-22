/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00155 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5736607567130802233808187817984000000000000 1278739410108715585021699607358106238976 4111938695335885148912615424000000000000))
theorem leaf00155_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5736607567130802233808187817984000000000000 1278739410108715585021699607358106238976 4111938695335885148912615424000000000000 raw00155=true := by decide +kernel
#print axioms leaf00155_raw
theorem leaf00155_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00155=true := by decide +kernel
#print axioms leaf00155_rectangular
def affine00155 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00155 (IntegerComputedClassCell.leftNumerator ![(109/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(109/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(109/32000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00155_transform : affine00155=(NestedInteger.clearedAll 3 raw00155 (IntegerComputedClassCell.leftNumerator ![(109/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(109/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(109/32000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00155_transform
theorem leaf00155_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00155=true := by decide +kernel
#print axioms leaf00155_sign
theorem leaf00155_log : RationalLog.accepts (730281/4294967296) (-18639138699/4294967296) 13 8=true := by decide +kernel
#print axioms leaf00155_log
def leaf00155 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (310982119349/1000000000000) (730281/4294967296) (-18639138699/4294967296) 13 8 ![60,0,4] ![(109/32000),0,0] ![(3/32000),1,(1/16)] affine00155
theorem leaf00155_checked : FastNestedCellData.accepts 1 2 4 leaf00155=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (310982119349/1000000000000) (730281/4294967296) (-18639138699/4294967296) 13 8 ![60,0,4] ![(109/32000),0,0] ![(3/32000),1,(1/16)] 5736607567130802233808187817984000000000000 1278739410108715585021699607358106238976 4111938695335885148912615424000000000000 raw00155 affine00155
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00155_raw leaf00155_rectangular
    leaf00155_transform leaf00155_sign leaf00155_log
#print axioms leaf00155_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
