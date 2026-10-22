/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01114 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3354913054498727601083777024000000000000 3988595279029569205550063373173252947968 21416991642489195997522034688000000000000))
theorem leaf01114_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3354913054498727601083777024000000000000 3988595279029569205550063373173252947968 21416991642489195997522034688000000000000 raw01114=true := by decide +kernel
#print axioms leaf01114_raw
theorem leaf01114_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01114=true := by decide +kernel
#print axioms leaf01114_rectangular
def affine01114 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01114 (IntegerComputedClassCell.leftNumerator ![(19/32),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/32),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/32),0,(15/16)] ![(1/32),1,(1/16)]))
theorem leaf01114_transform : affine01114=(NestedInteger.clearedAll 3 raw01114 (IntegerComputedClassCell.leftNumerator ![(19/32),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/32),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/32),0,(15/16)] ![(1/32),1,(1/16)])) := by decide +kernel
#print axioms leaf01114_transform
theorem leaf01114_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01114=true := by decide +kernel
#print axioms leaf01114_sign
theorem leaf01114_log : RationalLog.accepts (2152275201/2147483648) (4786215/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01114_log
def leaf01114 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (11639692871/62500000000) (2152275201/2147483648) (4786215/4294967296) 0 8 ![60,0,4] ![(19/32),0,(15/16)] ![(1/32),1,(1/16)] affine01114
theorem leaf01114_checked : FastNestedCellData.accepts 1 2 4 leaf01114=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (11639692871/62500000000) (2152275201/2147483648) (4786215/4294967296) 0 8 ![60,0,4] ![(19/32),0,(15/16)] ![(1/32),1,(1/16)] 3354913054498727601083777024000000000000 3988595279029569205550063373173252947968 21416991642489195997522034688000000000000 raw01114 affine01114
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01114_raw leaf01114_rectangular
    leaf01114_transform leaf01114_sign leaf01114_log
#print axioms leaf01114_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
