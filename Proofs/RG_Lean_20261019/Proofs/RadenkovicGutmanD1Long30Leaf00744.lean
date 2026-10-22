/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00744 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 541506356235279948327342309376000000000000 423591307855452325968716899841775425814528 3607474020333742041720592269312000000000000))
theorem leaf00744_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 541506356235279948327342309376000000000000 423591307855452325968716899841775425814528 3607474020333742041720592269312000000000000 raw00744=true := by decide +kernel
#print axioms leaf00744_raw
theorem leaf00744_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00744=true := by decide +kernel
#print axioms leaf00744_rectangular
def affine00744 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00744 (IntegerComputedClassCell.leftNumerator ![(209/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(209/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(209/6400),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00744_transform : affine00744=(NestedInteger.clearedAll 3 raw00744 (IntegerComputedClassCell.leftNumerator ![(209/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(209/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(209/6400),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00744_transform
theorem leaf00744_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00744=true := by decide +kernel
#print axioms leaf00744_sign
theorem leaf00744_log : RationalLog.accepts (1503338301/2147483648) (-382905577/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00744_log
def leaf00744 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (117420473569/1000000000000) (1503338301/2147483648) (-382905577/2147483648) 1 8 ![60,0,4] ![(209/6400),0,(1/2)] ![(3/6400),1,(1/2)] affine00744
theorem leaf00744_checked : FastNestedCellData.accepts 1 2 4 leaf00744=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (117420473569/1000000000000) (1503338301/2147483648) (-382905577/2147483648) 1 8 ![60,0,4] ![(209/6400),0,(1/2)] ![(3/6400),1,(1/2)] 541506356235279948327342309376000000000000 423591307855452325968716899841775425814528 3607474020333742041720592269312000000000000 raw00744 affine00744
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00744_raw leaf00744_rectangular
    leaf00744_transform leaf00744_sign leaf00744_log
#print axioms leaf00744_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
