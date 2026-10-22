/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00673 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 342190152044691867587051520000000000 230160540956120880461806199315103744 1211666578119406165405204480000000000))
theorem leaf00673_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 342190152044691867587051520000000000 230160540956120880461806199315103744 1211666578119406165405204480000000000 raw00673=true := by decide +kernel
#print axioms leaf00673_raw
theorem leaf00673_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00673=true := by decide +kernel
#print axioms leaf00673_rectangular
def affine00673 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00673 (IntegerComputedClassCell.leftNumerator ![(167/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(167/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(167/6400),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00673_transform : affine00673=(NestedInteger.clearedAll 3 raw00673 (IntegerComputedClassCell.leftNumerator ![(167/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(167/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(167/6400),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00673_transform
theorem leaf00673_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00673=true := by decide +kernel
#print axioms leaf00673_sign
theorem leaf00673_log : RationalLog.accepts (2427689629/4294967296) (-1225147845/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00673_log
def leaf00673 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (59360529/312500000) (2427689629/4294967296) (-1225147845/4294967296) 1 8 ![60,0,4] ![(167/6400),0,(1/4)] ![(3/6400),1,(1/4)] affine00673
theorem leaf00673_checked : FastNestedCellData.accepts 1 2 4 leaf00673=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (59360529/312500000) (2427689629/4294967296) (-1225147845/4294967296) 1 8 ![60,0,4] ![(167/6400),0,(1/4)] ![(3/6400),1,(1/4)] 342190152044691867587051520000000000 230160540956120880461806199315103744 1211666578119406165405204480000000000 raw00673 affine00673
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00673_raw leaf00673_rectangular
    leaf00673_transform leaf00673_sign leaf00673_log
#print axioms leaf00673_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
