/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01177 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 4230359786021662356935089848320000 5199389976023946324559430443597824 145102462887882143752519680000000000))
theorem leaf01177_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 4230359786021662356935089848320000 5199389976023946324559430443597824 145102462887882143752519680000000000 raw01177=true := by decide +kernel
#print axioms leaf01177_raw
theorem leaf01177_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01177=true := by decide +kernel
#print axioms leaf01177_rectangular
def affine01177 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01177 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/2),0,(3/4)] ![(1/16),1,(1/8)]))
theorem leaf01177_transform : affine01177=(NestedInteger.clearedAll 3 raw01177 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/2),0,(3/4)] ![(1/16),1,(1/8)])) := by decide +kernel
#print axioms leaf01177_transform
theorem leaf01177_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01177=true := by decide +kernel
#print axioms leaf01177_sign
theorem leaf01177_log : RationalLog.accepts (1274046875/1073741824) (91831109/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01177_log
def leaf01177 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1433301647/40000000000) (1274046875/1073741824) (91831109/1073741824) 0 8 ![60,0,4] ![(1/2),0,(3/4)] ![(1/16),1,(1/8)] affine01177
theorem leaf01177_checked : FastNestedCellData.accepts 1 2 4 leaf01177=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1433301647/40000000000) (1274046875/1073741824) (91831109/1073741824) 0 8 ![60,0,4] ![(1/2),0,(3/4)] ![(1/16),1,(1/8)] 4230359786021662356935089848320000 5199389976023946324559430443597824 145102462887882143752519680000000000 raw01177 affine01177
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01177_raw leaf01177_rectangular
    leaf01177_transform leaf01177_sign leaf01177_log
#print axioms leaf01177_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
