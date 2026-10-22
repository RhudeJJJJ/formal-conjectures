/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00598 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 665595280168697669998455291904000000000000 487581778463957028076265997193165162938368 3378290287774097492897712570368000000000000))
theorem leaf00598_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 665595280168697669998455291904000000000000 487581778463957028076265997193165162938368 3378290287774097492897712570368000000000000 raw00598=true := by decide +kernel
#print axioms leaf00598_raw
theorem leaf00598_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00598=true := by decide +kernel
#print axioms leaf00598_rectangular
def affine00598 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00598 (IntegerComputedClassCell.leftNumerator ![(31/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/1600),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00598_transform : affine00598=(NestedInteger.clearedAll 3 raw00598 (IntegerComputedClassCell.leftNumerator ![(31/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/1600),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00598_transform
theorem leaf00598_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00598=true := by decide +kernel
#print axioms leaf00598_sign
theorem leaf00598_log : RationalLog.accepts (1374727391/2147483648) (-957866455/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00598_log
def leaf00598 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (144327969751/1000000000000) (1374727391/2147483648) (-957866455/4294967296) 1 8 ![60,0,4] ![(31/1600),0,(1/4)] ![(1/3200),1,(1/4)] affine00598
theorem leaf00598_checked : FastNestedCellData.accepts 1 2 4 leaf00598=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (144327969751/1000000000000) (1374727391/2147483648) (-957866455/4294967296) 1 8 ![60,0,4] ![(31/1600),0,(1/4)] ![(1/3200),1,(1/4)] 665595280168697669998455291904000000000000 487581778463957028076265997193165162938368 3378290287774097492897712570368000000000000 raw00598 affine00598
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00598_raw leaf00598_rectangular
    leaf00598_transform leaf00598_sign leaf00598_log
#print axioms leaf00598_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
