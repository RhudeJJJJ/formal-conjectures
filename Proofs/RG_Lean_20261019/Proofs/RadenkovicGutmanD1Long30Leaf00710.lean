/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00710 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4030769029314436536480139575296000000000000 133226319604449734917633347531780428660736 152426981287706733179477950464000000000000))
theorem leaf00710_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4030769029314436536480139575296000000000000 133226319604449734917633347531780428660736 152426981287706733179477950464000000000000 raw00710=true := by decide +kernel
#print axioms leaf00710_raw
theorem leaf00710_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00710=true := by decide +kernel
#print axioms leaf00710_rectangular
def affine00710 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00710 (IntegerComputedClassCell.leftNumerator ![(191/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(191/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(191/6400),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00710_transform : affine00710=(NestedInteger.clearedAll 3 raw00710 (IntegerComputedClassCell.leftNumerator ![(191/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(191/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(191/6400),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00710_transform
theorem leaf00710_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00710=true := by decide +kernel
#print axioms leaf00710_sign
theorem leaf00710_log : RationalLog.accepts (75750339/4294967296) (-4335507921/2147483648) 6 8=true := by decide +kernel
#print axioms leaf00710_log
def leaf00710 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (437016853837/500000000000) (75750339/4294967296) (-4335507921/2147483648) 6 8 ![60,0,4] ![(191/6400),0,0] ![(3/6400),1,(1/16)] affine00710
theorem leaf00710_checked : FastNestedCellData.accepts 1 2 4 leaf00710=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (437016853837/500000000000) (75750339/4294967296) (-4335507921/2147483648) 6 8 ![60,0,4] ![(191/6400),0,0] ![(3/6400),1,(1/16)] 4030769029314436536480139575296000000000000 133226319604449734917633347531780428660736 152426981287706733179477950464000000000000 raw00710 affine00710
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00710_raw leaf00710_rectangular
    leaf00710_transform leaf00710_sign leaf00710_log
#print axioms leaf00710_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
