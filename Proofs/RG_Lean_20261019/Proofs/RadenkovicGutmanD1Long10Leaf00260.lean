/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00260 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 51232381943442510832467968000000000000 36071413847418019109196027323819753472 198179354296486701589069824000000000000))
theorem leaf00260_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 51232381943442510832467968000000000000 36071413847418019109196027323819753472 198179354296486701589069824000000000000 raw00260=true := by decide +kernel
#print axioms leaf00260_raw
theorem leaf00260_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00260=true := by decide +kernel
#print axioms leaf00260_rectangular
def affine00260 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00260 (IntegerComputedClassCell.leftNumerator ![(17/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/320),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00260_transform : affine00260=(NestedInteger.clearedAll 3 raw00260 (IntegerComputedClassCell.leftNumerator ![(17/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/320),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/320),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00260_transform
theorem leaf00260_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00260=true := by decide +kernel
#print axioms leaf00260_sign
theorem leaf00260_log : RationalLog.accepts (1279162939/2147483648) (-1112591665/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00260_log
def leaf00260 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (1421984251/7812500000) (1279162939/2147483648) (-1112591665/4294967296) 1 8 ![52,0,4] ![(17/320),0,(1/2)] ![(1/640),1,(1/2)] affine00260
theorem leaf00260_checked : FastNestedCellData.accepts 1 0 4 leaf00260=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (1421984251/7812500000) (1279162939/2147483648) (-1112591665/4294967296) 1 8 ![52,0,4] ![(17/320),0,(1/2)] ![(1/640),1,(1/2)] 51232381943442510832467968000000000000 36071413847418019109196027323819753472 198179354296486701589069824000000000000 raw00260 affine00260
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00260_raw leaf00260_rectangular
    leaf00260_transform leaf00260_sign leaf00260_log
#print axioms leaf00260_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
