/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00176 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6887122300787801396708429004800000000000 5253527628917418868901099225271098146816 43972683465576594886723895296000000000000))
theorem leaf00176_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6887122300787801396708429004800000000000 5253527628917418868901099225271098146816 43972683465576594886723895296000000000000 raw00176=true := by decide +kernel
#print axioms leaf00176_raw
theorem leaf00176_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00176=true := by decide +kernel
#print axioms leaf00176_rectangular
def affine00176 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00176 (IntegerComputedClassCell.leftNumerator ![(121/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(121/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(121/32000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00176_transform : affine00176=(NestedInteger.clearedAll 3 raw00176 (IntegerComputedClassCell.leftNumerator ![(121/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(121/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(121/32000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00176_transform
theorem leaf00176_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00176=true := by decide +kernel
#print axioms leaf00176_sign
theorem leaf00176_log : RationalLog.accepts (365821865/536870912) (-823798753/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00176_log
def leaf00176 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (119472527371/1000000000000) (365821865/536870912) (-823798753/4294967296) 1 8 ![60,0,4] ![(121/32000),0,(1/16)] ![(3/32000),1,(1/16)] affine00176
theorem leaf00176_checked : FastNestedCellData.accepts 1 2 4 leaf00176=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (119472527371/1000000000000) (365821865/536870912) (-823798753/4294967296) 1 8 ![60,0,4] ![(121/32000),0,(1/16)] ![(3/32000),1,(1/16)] 6887122300787801396708429004800000000000 5253527628917418868901099225271098146816 43972683465576594886723895296000000000000 raw00176 affine00176
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00176_raw leaf00176_rectangular
    leaf00176_transform leaf00176_sign leaf00176_log
#print axioms leaf00176_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
