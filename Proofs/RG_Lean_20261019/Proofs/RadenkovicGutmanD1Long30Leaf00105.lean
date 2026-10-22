/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00105 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1073107509831664076218093797376000000000000 99997665651249875853025395533915619328 429740573366769640655552512000000000000))
theorem leaf00105_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1073107509831664076218093797376000000000000 99997665651249875853025395533915619328 429740573366769640655552512000000000000 raw00105=true := by decide +kernel
#print axioms leaf00105_raw
theorem leaf00105_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00105=true := by decide +kernel
#print axioms leaf00105_rectangular
def affine00105 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00105 (IntegerComputedClassCell.leftNumerator ![(79/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(79/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(79/32000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00105_transform : affine00105=(NestedInteger.clearedAll 3 raw00105 (IntegerComputedClassCell.leftNumerator ![(79/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(79/32000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(79/32000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00105_transform
theorem leaf00105_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00105=true := by decide +kernel
#print axioms leaf00105_sign
theorem leaf00105_log : RationalLog.accepts (324677/4294967296) (-20379885865/4294967296) 14 8=true := by decide +kernel
#print axioms leaf00105_log
def leaf00105 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (116346549347/500000000000) (324677/4294967296) (-20379885865/4294967296) 14 8 ![60,0,4] ![(79/32000),0,0] ![(3/32000),1,(1/16)] affine00105
theorem leaf00105_checked : FastNestedCellData.accepts 1 2 4 leaf00105=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (116346549347/500000000000) (324677/4294967296) (-20379885865/4294967296) 14 8 ![60,0,4] ![(79/32000),0,0] ![(3/32000),1,(1/16)] 1073107509831664076218093797376000000000000 99997665651249875853025395533915619328 429740573366769640655552512000000000000 raw00105 affine00105
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00105_raw leaf00105_rectangular
    leaf00105_transform leaf00105_sign leaf00105_log
#print axioms leaf00105_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
