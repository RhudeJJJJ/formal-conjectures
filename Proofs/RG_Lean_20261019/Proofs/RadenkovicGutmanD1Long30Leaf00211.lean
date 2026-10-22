/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00211 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 642955463898334886759514505216000000000000 469780614329907981268780754797216497926144 3369565720303191807182489255936000000000000))
theorem leaf00211_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 642955463898334886759514505216000000000000 469780614329907981268780754797216497926144 3369565720303191807182489255936000000000000 raw00211=true := by decide +kernel
#print axioms leaf00211_raw
theorem leaf00211_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00211=true := by decide +kernel
#print axioms leaf00211_rectangular
def affine00211 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00211 (IntegerComputedClassCell.leftNumerator ![(71/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(71/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(71/16000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00211_transform : affine00211=(NestedInteger.clearedAll 3 raw00211 (IntegerComputedClassCell.leftNumerator ![(71/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(71/16000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(71/16000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00211_transform
theorem leaf00211_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00211=true := by decide +kernel
#print axioms leaf00211_sign
theorem leaf00211_log : RationalLog.accepts (2754169741/4294967296) (-954186953/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00211_log
def leaf00211 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (69709371077/500000000000) (2754169741/4294967296) (-954186953/4294967296) 1 8 ![60,0,4] ![(71/16000),0,(1/16)] ![(3/32000),1,(1/16)] affine00211
theorem leaf00211_checked : FastNestedCellData.accepts 1 2 4 leaf00211=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (69709371077/500000000000) (2754169741/4294967296) (-954186953/4294967296) 1 8 ![60,0,4] ![(71/16000),0,(1/16)] ![(3/32000),1,(1/16)] 642955463898334886759514505216000000000000 469780614329907981268780754797216497926144 3369565720303191807182489255936000000000000 raw00211 affine00211
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00211_raw leaf00211_rectangular
    leaf00211_transform leaf00211_sign leaf00211_log
#print axioms leaf00211_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
