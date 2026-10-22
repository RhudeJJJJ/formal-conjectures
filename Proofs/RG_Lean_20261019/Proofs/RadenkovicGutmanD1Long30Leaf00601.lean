/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00601 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9204307197007965451563330174976000000000000 3156500568198240220159104264360770563735552 6326077227083376983422724472832000000000000))
theorem leaf00601_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9204307197007965451563330174976000000000000 3156500568198240220159104264360770563735552 6326077227083376983422724472832000000000000 raw00601=true := by decide +kernel
#print axioms leaf00601_raw
theorem leaf00601_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00601=true := by decide +kernel
#print axioms leaf00601_rectangular
def affine00601 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00601 (IntegerComputedClassCell.leftNumerator ![(63/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(63/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(63/3200),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00601_transform : affine00601=(NestedInteger.clearedAll 3 raw00601 (IntegerComputedClassCell.leftNumerator ![(63/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(63/3200),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(63/3200),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00601_transform
theorem leaf00601_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00601=true := by decide +kernel
#print axioms leaf00601_sign
theorem leaf00601_log : RationalLog.accepts (982613447/4294967296) (-395937859/536870912) 3 8=true := by decide +kernel
#print axioms leaf00601_log
def leaf00601 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (498966492961/1000000000000) (982613447/4294967296) (-395937859/536870912) 3 8 ![60,0,4] ![(63/3200),0,(1/16)] ![(1/3200),1,(1/16)] affine00601
theorem leaf00601_checked : FastNestedCellData.accepts 1 2 4 leaf00601=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (498966492961/1000000000000) (982613447/4294967296) (-395937859/536870912) 3 8 ![60,0,4] ![(63/3200),0,(1/16)] ![(1/3200),1,(1/16)] 9204307197007965451563330174976000000000000 3156500568198240220159104264360770563735552 6326077227083376983422724472832000000000000 raw00601 affine00601
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00601_raw leaf00601_rectangular
    leaf00601_transform leaf00601_sign leaf00601_log
#print axioms leaf00601_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
