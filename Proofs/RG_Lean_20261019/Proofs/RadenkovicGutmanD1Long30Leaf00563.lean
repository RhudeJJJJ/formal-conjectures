/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00563 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 594809662506576560762120044544000000000000 448865439355601391942258831176963073245184 3480149367628348025916981510144000000000000))
theorem leaf00563_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 594809662506576560762120044544000000000000 448865439355601391942258831176963073245184 3480149367628348025916981510144000000000000 raw00563=true := by decide +kernel
#print axioms leaf00563_raw
theorem leaf00563_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00563=true := by decide +kernel
#print axioms leaf00563_rectangular
def affine00563 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00563 (IntegerComputedClassCell.leftNumerator ![(11/640),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/640),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/640),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00563_transform : affine00563=(NestedInteger.clearedAll 3 raw00563 (IntegerComputedClassCell.leftNumerator ![(11/640),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/640),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/640),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00563_transform
theorem leaf00563_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00563=true := by decide +kernel
#print axioms leaf00563_sign
theorem leaf00563_log : RationalLog.accepts (1435430723/2147483648) (-865074741/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00563_log
def leaf00563 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (128978785661/1000000000000) (1435430723/2147483648) (-865074741/4294967296) 1 8 ![60,0,4] ![(11/640),0,(1/4)] ![(1/3200),1,(1/4)] affine00563
theorem leaf00563_checked : FastNestedCellData.accepts 1 2 4 leaf00563=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (128978785661/1000000000000) (1435430723/2147483648) (-865074741/4294967296) 1 8 ![60,0,4] ![(11/640),0,(1/4)] ![(1/3200),1,(1/4)] 594809662506576560762120044544000000000000 448865439355601391942258831176963073245184 3480149367628348025916981510144000000000000 raw00563 affine00563
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00563_raw leaf00563_rectangular
    leaf00563_transform leaf00563_sign leaf00563_log
#print axioms leaf00563_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
