/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01223 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 47778282454689116799692177408000000000000 53711469857068377913082811920552948662272 5184372937724055821025527463936000000000000))
theorem leaf01223_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 47778282454689116799692177408000000000000 53711469857068377913082811920552948662272 5184372937724055821025527463936000000000000 raw01223=true := by decide +kernel
#print axioms leaf01223_raw
theorem leaf01223_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01223=true := by decide +kernel
#print axioms leaf01223_rectangular
def affine01223 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01223 (IntegerComputedClassCell.leftNumerator ![(19/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/64),0,(7/8)] ![(1/64),1,(1/16)]))
theorem leaf01223_transform : affine01223=(NestedInteger.clearedAll 3 raw01223 (IntegerComputedClassCell.leftNumerator ![(19/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/64),0,(7/8)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01223_transform
theorem leaf01223_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01223=true := by decide +kernel
#print axioms leaf01223_sign
theorem leaf01223_log : RationalLog.accepts (2389406891/2147483648) (229240469/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01223_log
def leaf01223 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (10360263527/1000000000000) (2389406891/2147483648) (229240469/4294967296) 0 8 ![60,0,4] ![(19/64),0,(7/8)] ![(1/64),1,(1/16)] affine01223
theorem leaf01223_checked : FastNestedCellData.accepts 1 2 4 leaf01223=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (10360263527/1000000000000) (2389406891/2147483648) (229240469/4294967296) 0 8 ![60,0,4] ![(19/64),0,(7/8)] ![(1/64),1,(1/16)] 47778282454689116799692177408000000000000 53711469857068377913082811920552948662272 5184372937724055821025527463936000000000000 raw01223 affine01223
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01223_raw leaf01223_rectangular
    leaf01223_transform leaf01223_sign leaf01223_log
#print axioms leaf01223_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
