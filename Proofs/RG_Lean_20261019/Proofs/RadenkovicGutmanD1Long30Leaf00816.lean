/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00816 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 633544482604727104858121830400000000000 158980400124134255275263158226599804928 226024877626460501226553344000000000000))
theorem leaf00816_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 633544482604727104858121830400000000000 158980400124134255275263158226599804928 226024877626460501226553344000000000000 raw00816=true := by decide +kernel
#print axioms leaf00816_raw
theorem leaf00816_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00816=true := by decide +kernel
#print axioms leaf00816_rectangular
def affine00816 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00816 (IntegerComputedClassCell.leftNumerator ![(29/640),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/640),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/640),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00816_transform : affine00816=(NestedInteger.clearedAll 3 raw00816 (IntegerComputedClassCell.leftNumerator ![(29/640),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/640),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/640),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00816_transform
theorem leaf00816_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00816=true := by decide +kernel
#print axioms leaf00816_sign
theorem leaf00816_log : RationalLog.accepts (316363155/2147483648) (-4112777597/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00816_log
def leaf00816 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (21980489741/31250000000) (316363155/2147483648) (-4112777597/4294967296) 3 8 ![60,0,4] ![(29/640),0,(1/16)] ![(3/3200),1,(1/16)] affine00816
theorem leaf00816_checked : FastNestedCellData.accepts 1 2 4 leaf00816=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (21980489741/31250000000) (316363155/2147483648) (-4112777597/4294967296) 3 8 ![60,0,4] ![(29/640),0,(1/16)] ![(3/3200),1,(1/16)] 633544482604727104858121830400000000000 158980400124134255275263158226599804928 226024877626460501226553344000000000000 raw00816 affine00816
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00816_raw leaf00816_rectangular
    leaf00816_transform leaf00816_sign leaf00816_log
#print axioms leaf00816_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
