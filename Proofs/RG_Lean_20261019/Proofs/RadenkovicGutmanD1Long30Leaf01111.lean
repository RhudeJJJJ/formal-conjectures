/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01111 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2194362076501288803949032243200000000000 2621861304467470445490241524304132964352 13775303138836081606376659353600000000000))
theorem leaf01111_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2194362076501288803949032243200000000000 2621861304467470445490241524304132964352 13775303138836081606376659353600000000000 raw01111=true := by decide +kernel
#print axioms leaf01111_raw
theorem leaf01111_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01111=true := by decide +kernel
#print axioms leaf01111_rectangular
def affine01111 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01111 (IntegerComputedClassCell.leftNumerator ![(19/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/32),0,(1/2)] ![(1/32),1,(1/4)]))
theorem leaf01111_transform : affine01111=(NestedInteger.clearedAll 3 raw01111 (IntegerComputedClassCell.leftNumerator ![(19/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/32),0,(1/2)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf01111_transform
theorem leaf01111_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01111=true := by decide +kernel
#print axioms leaf01111_sign
theorem leaf01111_log : RationalLog.accepts (538894451/536870912) (2019735/1073741824) 0 8=true := by decide +kernel
#print axioms leaf01111_log
def leaf01111 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (38066114089/200000000000) (538894451/536870912) (2019735/1073741824) 0 8 ![60,0,4] ![(19/32),0,(1/2)] ![(1/32),1,(1/4)] affine01111
theorem leaf01111_checked : FastNestedCellData.accepts 1 2 4 leaf01111=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (38066114089/200000000000) (538894451/536870912) (2019735/1073741824) 0 8 ![60,0,4] ![(19/32),0,(1/2)] ![(1/32),1,(1/4)] 2194362076501288803949032243200000000000 2621861304467470445490241524304132964352 13775303138836081606376659353600000000000 raw01111 affine01111
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01111_raw leaf01111_rectangular
    leaf01111_transform leaf01111_sign leaf01111_log
#print axioms leaf01111_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
