/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00838 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1460806930569192549062555992064000000000000 814006368894623784140728060406209242464256 2569772713824329690880845807616000000000000))
theorem leaf00838_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1460806930569192549062555992064000000000000 814006368894623784140728060406209242464256 2569772713824329690880845807616000000000000 raw00838=true := by decide +kernel
#print axioms leaf00838_raw
theorem leaf00838_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00838=true := by decide +kernel
#print axioms leaf00838_rectangular
def affine00838 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00838 (IntegerComputedClassCell.leftNumerator ![(157/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(157/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(157/3200),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00838_transform : affine00838=(NestedInteger.clearedAll 3 raw00838 (IntegerComputedClassCell.leftNumerator ![(157/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(157/3200),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(157/3200),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00838_transform
theorem leaf00838_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00838=true := by decide +kernel
#print axioms leaf00838_sign
theorem leaf00838_log : RationalLog.accepts (908777487/2147483648) (-923366211/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00838_log
def leaf00838 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (316762009541/1000000000000) (908777487/2147483648) (-923366211/2147483648) 2 8 ![60,0,4] ![(157/3200),0,(1/4)] ![(3/3200),1,(1/4)] affine00838
theorem leaf00838_checked : FastNestedCellData.accepts 1 2 4 leaf00838=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (316762009541/1000000000000) (908777487/2147483648) (-923366211/2147483648) 2 8 ![60,0,4] ![(157/3200),0,(1/4)] ![(3/3200),1,(1/4)] 1460806930569192549062555992064000000000000 814006368894623784140728060406209242464256 2569772713824329690880845807616000000000000 raw00838 affine00838
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00838_raw leaf00838_rectangular
    leaf00838_transform leaf00838_sign leaf00838_log
#print axioms leaf00838_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
