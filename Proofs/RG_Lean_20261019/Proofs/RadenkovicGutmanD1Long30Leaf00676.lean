/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00676 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 41477607695225907392282624000000000000 11915767695858397018555056170521853952 20215669496455646121295872000000000000))
theorem leaf00676_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 41477607695225907392282624000000000000 11915767695858397018555056170521853952 20215669496455646121295872000000000000 raw00676=true := by decide +kernel
#print axioms leaf00676_raw
theorem leaf00676_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00676=true := by decide +kernel
#print axioms leaf00676_rectangular
def affine00676 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00676 (IntegerComputedClassCell.leftNumerator ![(17/640),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/640),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/640),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00676_transform : affine00676=(NestedInteger.clearedAll 3 raw00676 (IntegerComputedClassCell.leftNumerator ![(17/640),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/640),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/640),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00676_transform
theorem leaf00676_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00676=true := by decide +kernel
#print axioms leaf00676_sign
theorem leaf00676_log : RationalLog.accepts (1516199/8388608) (-1836815885/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00676_log
def leaf00676 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (589432256891/1000000000000) (1516199/8388608) (-1836815885/2147483648) 3 8 ![60,0,4] ![(17/640),0,(1/16)] ![(3/6400),1,(1/16)] affine00676
theorem leaf00676_checked : FastNestedCellData.accepts 1 2 4 leaf00676=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (589432256891/1000000000000) (1516199/8388608) (-1836815885/2147483648) 3 8 ![60,0,4] ![(17/640),0,(1/16)] ![(3/6400),1,(1/16)] 41477607695225907392282624000000000000 11915767695858397018555056170521853952 20215669496455646121295872000000000000 raw00676 affine00676
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00676_raw leaf00676_rectangular
    leaf00676_transform leaf00676_sign leaf00676_log
#print axioms leaf00676_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
