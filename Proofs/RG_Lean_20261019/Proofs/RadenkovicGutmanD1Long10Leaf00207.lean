/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00207 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 533867540300228195827287746150400000000000 15138486476870976701081603874105531039744 26154033034590220221874700288000000000000))
theorem leaf00207_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 533867540300228195827287746150400000000000 15138486476870976701081603874105531039744 26154033034590220221874700288000000000000 raw00207=true := by decide +kernel
#print axioms leaf00207_raw
theorem leaf00207_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00207=true := by decide +kernel
#print axioms leaf00207_rectangular
def affine00207 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00207 (IntegerComputedClassCell.leftNumerator ![(7/200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/200),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00207_transform : affine00207=(NestedInteger.clearedAll 3 raw00207 (IntegerComputedClassCell.leftNumerator ![(7/200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/200),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00207_transform
theorem leaf00207_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00207=true := by decide +kernel
#print axioms leaf00207_sign
theorem leaf00207_log : RationalLog.accepts (38569685/2147483648) (-2157998551/1073741824) 6 8=true := by decide +kernel
#print axioms leaf00207_log
def leaf00207 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (578820347013/1000000000000) (38569685/2147483648) (-2157998551/1073741824) 6 8 ![52,0,4] ![(7/200),0,0] ![(3/3200),1,(1/4)] affine00207
theorem leaf00207_checked : FastNestedCellData.accepts 1 0 4 leaf00207=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (578820347013/1000000000000) (38569685/2147483648) (-2157998551/1073741824) 6 8 ![52,0,4] ![(7/200),0,0] ![(3/3200),1,(1/4)] 533867540300228195827287746150400000000000 15138486476870976701081603874105531039744 26154033034590220221874700288000000000000 raw00207 affine00207
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00207_raw leaf00207_rectangular
    leaf00207_transform leaf00207_sign leaf00207_log
#print axioms leaf00207_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
