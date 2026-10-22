/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01092 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 291603320054892211691728142336000000000000 328665858642448940711587567504502959374336 1299456865537825330838661758976000000000000))
theorem leaf01092_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 291603320054892211691728142336000000000000 328665858642448940711587567504502959374336 1299456865537825330838661758976000000000000 raw01092=true := by decide +kernel
#print axioms leaf01092_raw
theorem leaf01092_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01092=true := by decide +kernel
#print axioms leaf01092_rectangular
def affine01092 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01092 (IntegerComputedClassCell.leftNumerator ![(37/80),0,(1/8)] ![(3/80),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(37/80),0,(1/8)] ![(3/80),1,(1/8)]) (IntegerComputedClassCell.denominator ![(37/80),0,(1/8)] ![(3/80),1,(1/8)]))
theorem leaf01092_transform : affine01092=(NestedInteger.clearedAll 3 raw01092 (IntegerComputedClassCell.leftNumerator ![(37/80),0,(1/8)] ![(3/80),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(37/80),0,(1/8)] ![(3/80),1,(1/8)]) (IntegerComputedClassCell.denominator ![(37/80),0,(1/8)] ![(3/80),1,(1/8)])) := by decide +kernel
#print axioms leaf01092_transform
theorem leaf01092_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01092=true := by decide +kernel
#print axioms leaf01092_sign
theorem leaf01092_log : RationalLog.accepts (1931820293/2147483648) (-227276917/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01092_log
def leaf01092 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (126462781243/500000000000) (1931820293/2147483648) (-227276917/4294967296) 1 8 ![60,0,4] ![(37/80),0,(1/8)] ![(3/80),1,(1/8)] affine01092
theorem leaf01092_checked : FastNestedCellData.accepts 1 2 4 leaf01092=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (126462781243/500000000000) (1931820293/2147483648) (-227276917/4294967296) 1 8 ![60,0,4] ![(37/80),0,(1/8)] ![(3/80),1,(1/8)] 291603320054892211691728142336000000000000 328665858642448940711587567504502959374336 1299456865537825330838661758976000000000000 raw01092 affine01092
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01092_raw leaf01092_rectangular
    leaf01092_transform leaf01092_sign leaf01092_log
#print axioms leaf01092_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
