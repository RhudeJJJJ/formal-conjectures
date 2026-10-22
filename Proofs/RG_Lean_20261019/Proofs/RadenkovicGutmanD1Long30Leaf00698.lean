/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00698 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 37793541586680263524524343951360000000000 24775993524558541573707119222931979239424 120929765386288053951077023744000000000000))
theorem leaf00698_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 37793541586680263524524343951360000000000 24775993524558541573707119222931979239424 120929765386288053951077023744000000000000 raw00698=true := by decide +kernel
#print axioms leaf00698_raw
theorem leaf00698_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00698=true := by decide +kernel
#print axioms leaf00698_rectangular
def affine00698 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00698 (IntegerComputedClassCell.leftNumerator ![(91/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(91/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(91/3200),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00698_transform : affine00698=(NestedInteger.clearedAll 3 raw00698 (IntegerComputedClassCell.leftNumerator ![(91/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(91/3200),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(91/3200),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00698_transform
theorem leaf00698_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00698=true := by decide +kernel
#print axioms leaf00698_sign
theorem leaf00698_log : RationalLog.accepts (1168422325/2147483648) (-1307049555/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00698_log
def leaf00698 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (204879199471/1000000000000) (1168422325/2147483648) (-1307049555/4294967296) 1 8 ![60,0,4] ![(91/3200),0,(1/4)] ![(3/6400),1,(1/4)] affine00698
theorem leaf00698_checked : FastNestedCellData.accepts 1 2 4 leaf00698=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (204879199471/1000000000000) (1168422325/2147483648) (-1307049555/4294967296) 1 8 ![60,0,4] ![(91/3200),0,(1/4)] ![(3/6400),1,(1/4)] 37793541586680263524524343951360000000000 24775993524558541573707119222931979239424 120929765386288053951077023744000000000000 raw00698 affine00698
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00698_raw leaf00698_rectangular
    leaf00698_transform leaf00698_sign leaf00698_log
#print axioms leaf00698_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
