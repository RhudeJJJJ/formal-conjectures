/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00925 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 948116210307163428133705613312000000000000 202424373872075981676978749968731479212032 246150641827001658973184065536000000000000))
theorem leaf00925_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 948116210307163428133705613312000000000000 202424373872075981676978749968731479212032 246150641827001658973184065536000000000000 raw00925=true := by decide +kernel
#print axioms leaf00925_raw
theorem leaf00925_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00925=true := by decide +kernel
#print axioms leaf00925_rectangular
def affine00925 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00925 (IntegerComputedClassCell.leftNumerator ![(13/160),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/160),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/160),0,0] ![(1/320),1,(1/16)]))
theorem leaf00925_transform : affine00925=(NestedInteger.clearedAll 3 raw00925 (IntegerComputedClassCell.leftNumerator ![(13/160),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/160),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/160),0,0] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00925_transform
theorem leaf00925_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00925=true := by decide +kernel
#print axioms leaf00925_sign
theorem leaf00925_log : RationalLog.accepts (125796047/1073741824) (-4604726789/4294967296) 4 8=true := by decide +kernel
#print axioms leaf00925_log
def leaf00925 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (822359723987/1000000000000) (125796047/1073741824) (-4604726789/4294967296) 4 8 ![60,0,4] ![(13/160),0,0] ![(1/320),1,(1/16)] affine00925
theorem leaf00925_checked : FastNestedCellData.accepts 1 2 4 leaf00925=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (822359723987/1000000000000) (125796047/1073741824) (-4604726789/4294967296) 4 8 ![60,0,4] ![(13/160),0,0] ![(1/320),1,(1/16)] 948116210307163428133705613312000000000000 202424373872075981676978749968731479212032 246150641827001658973184065536000000000000 raw00925 affine00925
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00925_raw leaf00925_rectangular
    leaf00925_transform leaf00925_sign leaf00925_log
#print axioms leaf00925_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
