/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00886 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 26917207099204719728452289167360000000000 7439855675816338763282946461025504854016 10197277384039911399221310259200000000000))
theorem leaf00886_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 26917207099204719728452289167360000000000 7439855675816338763282946461025504854016 10197277384039911399221310259200000000000 raw00886=true := by decide +kernel
#print axioms leaf00886_raw
theorem leaf00886_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00886=true := by decide +kernel
#print axioms leaf00886_rectangular
def affine00886 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00886 (IntegerComputedClassCell.leftNumerator ![(41/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/640),0,(1/16)] ![(1/640),1,(1/16)]))
theorem leaf00886_transform : affine00886=(NestedInteger.clearedAll 3 raw00886 (IntegerComputedClassCell.leftNumerator ![(41/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/640),0,(1/16)] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00886_transform
theorem leaf00886_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00886=true := by decide +kernel
#print axioms leaf00886_sign
theorem leaf00886_log : RationalLog.accepts (343178935/2147483648) (-3938055731/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00886_log
def leaf00886 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (145918472071/200000000000) (343178935/2147483648) (-3938055731/4294967296) 3 8 ![60,0,4] ![(41/640),0,(1/16)] ![(1/640),1,(1/16)] affine00886
theorem leaf00886_checked : FastNestedCellData.accepts 1 2 4 leaf00886=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (145918472071/200000000000) (343178935/2147483648) (-3938055731/4294967296) 3 8 ![60,0,4] ![(41/640),0,(1/16)] ![(1/640),1,(1/16)] 26917207099204719728452289167360000000000 7439855675816338763282946461025504854016 10197277384039911399221310259200000000000 raw00886 affine00886
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00886_raw leaf00886_rectangular
    leaf00886_transform leaf00886_sign leaf00886_log
#print axioms leaf00886_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
