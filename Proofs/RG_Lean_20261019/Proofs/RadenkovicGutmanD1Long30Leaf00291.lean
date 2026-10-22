/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00291 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 187304042821141901109209176473600000000000 119066740758998378310294048116808584527872 586317748776335386596727586816000000000000))
theorem leaf00291_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 187304042821141901109209176473600000000000 119066740758998378310294048116808584527872 586317748776335386596727586816000000000000 raw00291=true := by decide +kernel
#print axioms leaf00291_raw
theorem leaf00291_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00291=true := by decide +kernel
#print axioms leaf00291_rectangular
def affine00291 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00291 (IntegerComputedClassCell.leftNumerator ![(21/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/3200),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00291_transform : affine00291=(NestedInteger.clearedAll 3 raw00291 (IntegerComputedClassCell.leftNumerator ![(21/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/3200),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00291_transform
theorem leaf00291_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00291=true := by decide +kernel
#print axioms leaf00291_sign
theorem leaf00291_log : RationalLog.accepts (2269396135/4294967296) (-1369944633/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00291_log
def leaf00291 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (101537725071/500000000000) (2269396135/4294967296) (-1369944633/4294967296) 1 8 ![60,0,4] ![(21/3200),0,(1/16)] ![(1/6400),1,(1/16)] affine00291
theorem leaf00291_checked : FastNestedCellData.accepts 1 2 4 leaf00291=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (101537725071/500000000000) (2269396135/4294967296) (-1369944633/4294967296) 1 8 ![60,0,4] ![(21/3200),0,(1/16)] ![(1/6400),1,(1/16)] 187304042821141901109209176473600000000000 119066740758998378310294048116808584527872 586317748776335386596727586816000000000000 raw00291 affine00291
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00291_raw leaf00291_rectangular
    leaf00291_transform leaf00291_sign leaf00291_log
#print axioms leaf00291_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
