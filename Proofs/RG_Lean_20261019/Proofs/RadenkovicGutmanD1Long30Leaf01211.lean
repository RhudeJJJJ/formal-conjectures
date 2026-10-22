/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01211 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 488658864504427458909437952000000000000 558297788082981825842232000029638262784 42491119332138058954867474432000000000000))
theorem leaf01211_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 488658864504427458909437952000000000000 558297788082981825842232000029638262784 42491119332138058954867474432000000000000 raw01211=true := by decide +kernel
#print axioms leaf01211_raw
theorem leaf01211_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01211=true := by decide +kernel
#print axioms leaf01211_rectangular
def affine01211 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01211 (IntegerComputedClassCell.leftNumerator ![(21/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/64),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf01211_transform : affine01211=(NestedInteger.clearedAll 3 raw01211 (IntegerComputedClassCell.leftNumerator ![(21/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/64),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf01211_transform
theorem leaf01211_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01211=true := by decide +kernel
#print axioms leaf01211_sign
theorem leaf01211_log : RationalLog.accepts (2421703043/2147483648) (258072277/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01211_log
def leaf01211 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (6569582031/500000000000) (2421703043/2147483648) (258072277/4294967296) 0 8 ![60,0,4] ![(21/64),0,(1/2)] ![(1/64),1,(1/4)] affine01211
theorem leaf01211_checked : FastNestedCellData.accepts 1 2 4 leaf01211=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (6569582031/500000000000) (2421703043/2147483648) (258072277/4294967296) 0 8 ![60,0,4] ![(21/64),0,(1/2)] ![(1/64),1,(1/4)] 488658864504427458909437952000000000000 558297788082981825842232000029638262784 42491119332138058954867474432000000000000 raw01211 affine01211
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01211_raw leaf01211_rectangular
    leaf01211_transform leaf01211_sign leaf01211_log
#print axioms leaf01211_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
