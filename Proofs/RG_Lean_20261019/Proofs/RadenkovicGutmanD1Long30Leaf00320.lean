/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00320 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2575325132430345499431665664000000000000 4265057543256249075975252563472678912 7458519050911365220794368000000000000))
theorem leaf00320_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2575325132430345499431665664000000000000 4265057543256249075975252563472678912 7458519050911365220794368000000000000 raw00320=true := by decide +kernel
#print axioms leaf00320_raw
theorem leaf00320_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00320=true := by decide +kernel
#print axioms leaf00320_rectangular
def affine00320 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00320 (IntegerComputedClassCell.leftNumerator ![(3/400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00320_transform : affine00320=(NestedInteger.clearedAll 3 raw00320 (IntegerComputedClassCell.leftNumerator ![(3/400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00320_transform
theorem leaf00320_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00320=true := by decide +kernel
#print axioms leaf00320_sign
theorem leaf00320_log : RationalLog.accepts (4525277/4294967296) (-14722118373/4294967296) 10 8=true := by decide +kernel
#print axioms leaf00320_log
def leaf00320 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (8934953931/15625000000) (4525277/4294967296) (-14722118373/4294967296) 10 8 ![60,0,4] ![(3/400),0,0] ![(1/6400),1,(1/16)] affine00320
theorem leaf00320_checked : FastNestedCellData.accepts 1 2 4 leaf00320=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (8934953931/15625000000) (4525277/4294967296) (-14722118373/4294967296) 10 8 ![60,0,4] ![(3/400),0,0] ![(1/6400),1,(1/16)] 2575325132430345499431665664000000000000 4265057543256249075975252563472678912 7458519050911365220794368000000000000 raw00320 affine00320
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00320_raw leaf00320_rectangular
    leaf00320_transform leaf00320_sign leaf00320_log
#print axioms leaf00320_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
