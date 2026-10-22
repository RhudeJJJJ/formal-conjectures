/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00870 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 62190014849630343702645833728000000000000 7681006877447063293700196631638802694144 8899738594947494613591523328000000000000))
theorem leaf00870_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 62190014849630343702645833728000000000000 7681006877447063293700196631638802694144 8899738594947494613591523328000000000000 raw00870=true := by decide +kernel
#print axioms leaf00870_raw
theorem leaf00870_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00870=true := by decide +kernel
#print axioms leaf00870_rectangular
def affine00870 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00870 (IntegerComputedClassCell.leftNumerator ![(19/320),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/320),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/320),0,0] ![(1/640),1,(1/16)]))
theorem leaf00870_transform : affine00870=(NestedInteger.clearedAll 3 raw00870 (IntegerComputedClassCell.leftNumerator ![(19/320),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/320),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/320),0,0] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00870_transform
theorem leaf00870_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00870=true := by decide +kernel
#print axioms leaf00870_sign
theorem leaf00870_log : RationalLog.accepts (142364123/2147483648) (-5827549245/4294967296) 4 8=true := by decide +kernel
#print axioms leaf00870_log
def leaf00870 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (107882478731/125000000000) (142364123/2147483648) (-5827549245/4294967296) 4 8 ![60,0,4] ![(19/320),0,0] ![(1/640),1,(1/16)] affine00870
theorem leaf00870_checked : FastNestedCellData.accepts 1 2 4 leaf00870=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (107882478731/125000000000) (142364123/2147483648) (-5827549245/4294967296) 4 8 ![60,0,4] ![(19/320),0,0] ![(1/640),1,(1/16)] 62190014849630343702645833728000000000000 7681006877447063293700196631638802694144 8899738594947494613591523328000000000000 raw00870 affine00870
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00870_raw leaf00870_rectangular
    leaf00870_transform leaf00870_sign leaf00870_log
#print axioms leaf00870_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
