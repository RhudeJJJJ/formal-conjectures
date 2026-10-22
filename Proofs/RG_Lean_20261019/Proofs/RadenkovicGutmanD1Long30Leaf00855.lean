/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00855 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 40095803600763594086156546867200000000000 4259850488024069267995518849893074468864 4899538398536439211685104844800000000000))
theorem leaf00855_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 40095803600763594086156546867200000000000 4259850488024069267995518849893074468864 4899538398536439211685104844800000000000 raw00855=true := by decide +kernel
#print axioms leaf00855_raw
theorem leaf00855_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00855=true := by decide +kernel
#print axioms leaf00855_rectangular
def affine00855 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00855 (IntegerComputedClassCell.leftNumerator ![(7/128),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/128),0,0] ![(1/640),1,(1/16)]))
theorem leaf00855_transform : affine00855=(NestedInteger.clearedAll 3 raw00855 (IntegerComputedClassCell.leftNumerator ![(7/128),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/128),0,0] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00855_transform
theorem leaf00855_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00855=true := by decide +kernel
#print axioms leaf00855_sign
theorem leaf00855_log : RationalLog.accepts (122043307/2147483648) (-6158287671/4294967296) 5 8=true := by decide +kernel
#print axioms leaf00855_log
def leaf00855 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (86943914743/100000000000) (122043307/2147483648) (-6158287671/4294967296) 5 8 ![60,0,4] ![(7/128),0,0] ![(1/640),1,(1/16)] affine00855
theorem leaf00855_checked : FastNestedCellData.accepts 1 2 4 leaf00855=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (86943914743/100000000000) (122043307/2147483648) (-6158287671/4294967296) 5 8 ![60,0,4] ![(7/128),0,0] ![(1/640),1,(1/16)] 40095803600763594086156546867200000000000 4259850488024069267995518849893074468864 4899538398536439211685104844800000000000 raw00855 affine00855
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00855_raw leaf00855_rectangular
    leaf00855_transform leaf00855_sign leaf00855_log
#print axioms leaf00855_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
