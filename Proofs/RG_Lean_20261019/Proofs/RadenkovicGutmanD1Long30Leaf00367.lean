/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00367 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2533277846477218063498270998528000000000000 1866806684263396182123670343719617835302912 13593655029820224411272493400064000000000000))
theorem leaf00367_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2533277846477218063498270998528000000000000 1866806684263396182123670343719617835302912 13593655029820224411272493400064000000000000 raw00367=true := by decide +kernel
#print axioms leaf00367_raw
theorem leaf00367_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00367=true := by decide +kernel
#print axioms leaf00367_rectangular
def affine00367 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00367 (IntegerComputedClassCell.leftNumerator ![(57/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(57/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(57/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00367_transform : affine00367=(NestedInteger.clearedAll 3 raw00367 (IntegerComputedClassCell.leftNumerator ![(57/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(57/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(57/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00367_transform
theorem leaf00367_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00367=true := by decide +kernel
#print axioms leaf00367_sign
theorem leaf00367_log : RationalLog.accepts (2782852373/4294967296) (-465969079/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00367_log
def leaf00367 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (137329267233/1000000000000) (2782852373/4294967296) (-465969079/2147483648) 1 8 ![60,0,4] ![(57/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00367
theorem leaf00367_checked : FastNestedCellData.accepts 1 2 4 leaf00367=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (137329267233/1000000000000) (2782852373/4294967296) (-465969079/2147483648) 1 8 ![60,0,4] ![(57/6400),0,(1/8)] ![(1/6400),1,(1/8)] 2533277846477218063498270998528000000000000 1866806684263396182123670343719617835302912 13593655029820224411272493400064000000000000 raw00367 affine00367
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00367_raw leaf00367_rectangular
    leaf00367_transform leaf00367_sign leaf00367_log
#print axioms leaf00367_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
