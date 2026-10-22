/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00885 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 631477297761228771972870465126400000000000 89434039729689276619800470223724212125696 104502052455121028780685629849600000000000))
theorem leaf00885_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 631477297761228771972870465126400000000000 89434039729689276619800470223724212125696 104502052455121028780685629849600000000000 raw00885=true := by decide +kernel
#print axioms leaf00885_raw
theorem leaf00885_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00885=true := by decide +kernel
#print axioms leaf00885_rectangular
def affine00885 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00885 (IntegerComputedClassCell.leftNumerator ![(41/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/640),0,0] ![(1/640),1,(1/16)]))
theorem leaf00885_transform : affine00885=(NestedInteger.clearedAll 3 raw00885 (IntegerComputedClassCell.leftNumerator ![(41/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/640),0,0] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00885_transform
theorem leaf00885_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00885=true := by decide +kernel
#print axioms leaf00885_sign
theorem leaf00885_log : RationalLog.accepts (327771469/4294967296) (-5525223443/4294967296) 4 8=true := by decide +kernel
#print axioms leaf00885_log
def leaf00885 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (171162264527/200000000000) (327771469/4294967296) (-5525223443/4294967296) 4 8 ![60,0,4] ![(41/640),0,0] ![(1/640),1,(1/16)] affine00885
theorem leaf00885_checked : FastNestedCellData.accepts 1 2 4 leaf00885=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (171162264527/200000000000) (327771469/4294967296) (-5525223443/4294967296) 4 8 ![60,0,4] ![(41/640),0,0] ![(1/640),1,(1/16)] 631477297761228771972870465126400000000000 89434039729689276619800470223724212125696 104502052455121028780685629849600000000000 raw00885 affine00885
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00885_raw leaf00885_rectangular
    leaf00885_transform leaf00885_sign leaf00885_log
#print axioms leaf00885_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
