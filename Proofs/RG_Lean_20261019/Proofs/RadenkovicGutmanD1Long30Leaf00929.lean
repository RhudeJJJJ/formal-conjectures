/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00929 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 232895318861184028354183744716800000000000 154365953260084756039779847946518308847616 611336725745926251160373559296000000000000))
theorem leaf00929_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 232895318861184028354183744716800000000000 154365953260084756039779847946518308847616 611336725745926251160373559296000000000000 raw00929=true := by decide +kernel
#print axioms leaf00929_raw
theorem leaf00929_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00929=true := by decide +kernel
#print axioms leaf00929_rectangular
def affine00929 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00929 (IntegerComputedClassCell.leftNumerator ![(13/160),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/160),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/160),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00929_transform : affine00929=(NestedInteger.clearedAll 3 raw00929 (IntegerComputedClassCell.leftNumerator ![(13/160),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/160),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/160),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00929_transform
theorem leaf00929_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00929=true := by decide +kernel
#print axioms leaf00929_sign
theorem leaf00929_log : RationalLog.accepts (1136425435/2147483648) (-1366677973/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00929_log
def leaf00929 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (252505610671/1000000000000) (1136425435/2147483648) (-1366677973/4294967296) 1 8 ![60,0,4] ![(13/160),0,(1/2)] ![(1/320),1,(1/2)] affine00929
theorem leaf00929_checked : FastNestedCellData.accepts 1 2 4 leaf00929=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (252505610671/1000000000000) (1136425435/2147483648) (-1366677973/4294967296) 1 8 ![60,0,4] ![(13/160),0,(1/2)] ![(1/320),1,(1/2)] 232895318861184028354183744716800000000000 154365953260084756039779847946518308847616 611336725745926251160373559296000000000000 raw00929 affine00929
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00929_raw leaf00929_rectangular
    leaf00929_transform leaf00929_sign leaf00929_log
#print axioms leaf00929_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
