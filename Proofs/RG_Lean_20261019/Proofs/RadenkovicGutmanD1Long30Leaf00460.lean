/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00460 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3327817040463676613340455501824000000000000 15891862490228484372734656659420524576768 22022929494569159199794659328000000000000))
theorem leaf00460_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3327817040463676613340455501824000000000000 15891862490228484372734656659420524576768 22022929494569159199794659328000000000000 raw00460=true := by decide +kernel
#print axioms leaf00460_raw
theorem leaf00460_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00460=true := by decide +kernel
#print axioms leaf00460_rectangular
def affine00460 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00460 (IntegerComputedClassCell.leftNumerator ![(19/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/1600),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00460_transform : affine00460=(NestedInteger.clearedAll 3 raw00460 (IntegerComputedClassCell.leftNumerator ![(19/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/1600),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00460_transform
theorem leaf00460_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00460=true := by decide +kernel
#print axioms leaf00460_sign
theorem leaf00460_log : RationalLog.accepts (5956781/2147483648) (-12643357121/4294967296) 9 8=true := by decide +kernel
#print axioms leaf00460_log
def leaf00460 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (721605292981/1000000000000) (5956781/2147483648) (-12643357121/4294967296) 9 8 ![60,0,4] ![(19/1600),0,0] ![(1/6400),1,(1/16)] affine00460
theorem leaf00460_checked : FastNestedCellData.accepts 1 2 4 leaf00460=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (721605292981/1000000000000) (5956781/2147483648) (-12643357121/4294967296) 9 8 ![60,0,4] ![(19/1600),0,0] ![(1/6400),1,(1/16)] 3327817040463676613340455501824000000000000 15891862490228484372734656659420524576768 22022929494569159199794659328000000000000 raw00460 affine00460
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00460_raw leaf00460_rectangular
    leaf00460_transform leaf00460_sign leaf00460_log
#print axioms leaf00460_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
