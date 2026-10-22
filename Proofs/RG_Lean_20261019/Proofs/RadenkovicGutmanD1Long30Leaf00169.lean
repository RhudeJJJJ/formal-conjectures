/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00169 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 309827648869142186791272448000000000 300109193127155939202097208761516032 22335149477420840894783815680000000000))
theorem leaf00169_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 309827648869142186791272448000000000 300109193127155939202097208761516032 22335149477420840894783815680000000000 raw00169=true := by decide +kernel
#print axioms leaf00169_raw
theorem leaf00169_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00169=true := by decide +kernel
#print axioms leaf00169_rectangular
def affine00169 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00169 (IntegerComputedClassCell.leftNumerator ![(23/6400),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/6400),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/6400),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00169_transform : affine00169=(NestedInteger.clearedAll 3 raw00169 (IntegerComputedClassCell.leftNumerator ![(23/6400),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/6400),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/6400),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00169_transform
theorem leaf00169_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00169=true := by decide +kernel
#print axioms leaf00169_sign
theorem leaf00169_log : RationalLog.accepts (4105087235/4294967296) (-24275673/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00169_log
def leaf00169 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (33591581/2500000000) (4105087235/4294967296) (-24275673/1073741824) 1 8 ![60,0,4] ![(23/6400),0,(1/2)] ![(3/32000),1,(1/2)] affine00169
theorem leaf00169_checked : FastNestedCellData.accepts 1 2 4 leaf00169=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (33591581/2500000000) (4105087235/4294967296) (-24275673/1073741824) 1 8 ![60,0,4] ![(23/6400),0,(1/2)] ![(3/32000),1,(1/2)] 309827648869142186791272448000000000 300109193127155939202097208761516032 22335149477420840894783815680000000000 raw00169 affine00169
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00169_raw leaf00169_rectangular
    leaf00169_transform leaf00169_sign leaf00169_log
#print axioms leaf00169_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
