/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00684 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1133937545459435118888432435200000000000 917889462098550785912805502915587342336 9332564248736113911604759756800000000000))
theorem leaf00684_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1133937545459435118888432435200000000000 917889462098550785912805502915587342336 9332564248736113911604759756800000000000 raw00684=true := by decide +kernel
#print axioms leaf00684_raw
theorem leaf00684_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00684=true := by decide +kernel
#print axioms leaf00684_rectangular
def affine00684 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00684 (IntegerComputedClassCell.leftNumerator ![(173/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(173/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(173/6400),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00684_transform : affine00684=(NestedInteger.clearedAll 3 raw00684 (IntegerComputedClassCell.leftNumerator ![(173/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(173/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(173/6400),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00684_transform
theorem leaf00684_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00684=true := by decide +kernel
#print axioms leaf00684_sign
theorem leaf00684_log : RationalLog.accepts (1582665057/2147483648) (-327691623/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00684_log
def leaf00684 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4917670201/50000000000) (1582665057/2147483648) (-327691623/2147483648) 1 8 ![60,0,4] ![(173/6400),0,(1/2)] ![(3/6400),1,(1/2)] affine00684
theorem leaf00684_checked : FastNestedCellData.accepts 1 2 4 leaf00684=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4917670201/50000000000) (1582665057/2147483648) (-327691623/2147483648) 1 8 ![60,0,4] ![(173/6400),0,(1/2)] ![(3/6400),1,(1/2)] 1133937545459435118888432435200000000000 917889462098550785912805502915587342336 9332564248736113911604759756800000000000 raw00684 affine00684
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00684_raw leaf00684_rectangular
    leaf00684_transform leaf00684_sign leaf00684_log
#print axioms leaf00684_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
