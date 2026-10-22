/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00381 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1294012438029640124790135062528000000000000 698928316634671933382680694846854212354048 2490886370933999240753933451264000000000000))
theorem leaf00381_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1294012438029640124790135062528000000000000 698928316634671933382680694846854212354048 2490886370933999240753933451264000000000000 raw00381=true := by decide +kernel
#print axioms leaf00381_raw
theorem leaf00381_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00381=true := by decide +kernel
#print axioms leaf00381_rectangular
def affine00381 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00381 (IntegerComputedClassCell.leftNumerator ![(3/320),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/320),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/320),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00381_transform : affine00381=(NestedInteger.clearedAll 3 raw00381 (IntegerComputedClassCell.leftNumerator ![(3/320),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/320),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/320),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00381_transform
theorem leaf00381_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00381=true := by decide +kernel
#print axioms leaf00381_sign
theorem leaf00381_log : RationalLog.accepts (905758699/2147483648) (-926938917/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00381_log
def leaf00381 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (280594219307/1000000000000) (905758699/2147483648) (-926938917/2147483648) 2 8 ![60,0,4] ![(3/320),0,(1/16)] ![(1/6400),1,(1/16)] affine00381
theorem leaf00381_checked : FastNestedCellData.accepts 1 2 4 leaf00381=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (280594219307/1000000000000) (905758699/2147483648) (-926938917/2147483648) 2 8 ![60,0,4] ![(3/320),0,(1/16)] ![(1/6400),1,(1/16)] 1294012438029640124790135062528000000000000 698928316634671933382680694846854212354048 2490886370933999240753933451264000000000000 raw00381 affine00381
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00381_raw leaf00381_rectangular
    leaf00381_transform leaf00381_sign leaf00381_log
#print axioms leaf00381_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
