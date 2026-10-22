/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01003 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 85176314911170018794439232716800000000000 54290451275568245954822695178114319777792 117577528608868166445365093990400000000000))
theorem leaf01003_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 85176314911170018794439232716800000000000 54290451275568245954822695178114319777792 117577528608868166445365093990400000000000 raw01003=true := by decide +kernel
#print axioms leaf01003_raw
theorem leaf01003_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01003=true := by decide +kernel
#print axioms leaf01003_rectangular
def affine01003 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01003 (IntegerComputedClassCell.leftNumerator ![(3/20),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/20),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/20),0,(1/4)] ![(1/160),1,(1/4)]))
theorem leaf01003_transform : affine01003=(NestedInteger.clearedAll 3 raw01003 (IntegerComputedClassCell.leftNumerator ![(3/20),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/20),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/20),0,(1/4)] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf01003_transform
theorem leaf01003_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01003=true := by decide +kernel
#print axioms leaf01003_sign
theorem leaf01003_log : RationalLog.accepts (936405219/2147483648) (-891209755/2147483648) 2 8=true := by decide +kernel
#print axioms leaf01003_log
def leaf01003 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (92348345671/200000000000) (936405219/2147483648) (-891209755/2147483648) 2 8 ![60,0,4] ![(3/20),0,(1/4)] ![(1/160),1,(1/4)] affine01003
theorem leaf01003_checked : FastNestedCellData.accepts 1 2 4 leaf01003=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (92348345671/200000000000) (936405219/2147483648) (-891209755/2147483648) 2 8 ![60,0,4] ![(3/20),0,(1/4)] ![(1/160),1,(1/4)] 85176314911170018794439232716800000000000 54290451275568245954822695178114319777792 117577528608868166445365093990400000000000 raw01003 affine01003
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01003_raw leaf01003_rectangular
    leaf01003_transform leaf01003_sign leaf01003_log
#print axioms leaf01003_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
