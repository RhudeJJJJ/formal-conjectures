/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00126 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 104474081282579620490238754816000000000000 84853148606688631820669644403169063600128 936395118877816797192318353408000000000000))
theorem leaf00126_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 104474081282579620490238754816000000000000 84853148606688631820669644403169063600128 936395118877816797192318353408000000000000 raw00126=true := by decide +kernel
#print axioms leaf00126_raw
theorem leaf00126_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00126=true := by decide +kernel
#print axioms leaf00126_rectangular
def affine00126 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00126 (IntegerComputedClassCell.leftNumerator ![(91/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(91/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(91/32000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00126_transform : affine00126=(NestedInteger.clearedAll 3 raw00126 (IntegerComputedClassCell.leftNumerator ![(91/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(91/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(91/32000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00126_transform
theorem leaf00126_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00126=true := by decide +kernel
#print axioms leaf00126_sign
theorem leaf00126_log : RationalLog.accepts (3198505273/4294967296) (-632993051/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00126_log
def leaf00126 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (22654205179/250000000000) (3198505273/4294967296) (-632993051/4294967296) 1 8 ![60,0,4] ![(91/32000),0,(1/16)] ![(3/32000),1,(1/16)] affine00126
theorem leaf00126_checked : FastNestedCellData.accepts 1 2 4 leaf00126=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (22654205179/250000000000) (3198505273/4294967296) (-632993051/4294967296) 1 8 ![60,0,4] ![(91/32000),0,(1/16)] ![(3/32000),1,(1/16)] 104474081282579620490238754816000000000000 84853148606688631820669644403169063600128 936395118877816797192318353408000000000000 raw00126 affine00126
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00126_raw leaf00126_rectangular
    leaf00126_transform leaf00126_sign leaf00126_log
#print axioms leaf00126_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
