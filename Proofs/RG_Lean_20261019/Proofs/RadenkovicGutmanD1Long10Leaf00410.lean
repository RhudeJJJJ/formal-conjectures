/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00410 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 1706332769965681155534009401344000000000000 2335139850522862591123391850050272144392192 25244622829216360881823665881088000000000000))
theorem leaf00410_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 1706332769965681155534009401344000000000000 2335139850522862591123391850050272144392192 25244622829216360881823665881088000000000000 raw00410=true := by decide +kernel
#print axioms leaf00410_raw
theorem leaf00410_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00410=true := by decide +kernel
#print axioms leaf00410_rectangular
def affine00410 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00410 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(3/4)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(3/4)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/4),0,(3/4)] ![(1/8),1,(1/4)]))
theorem leaf00410_transform : affine00410=(NestedInteger.clearedAll 3 raw00410 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(3/4)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(3/4)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/4),0,(3/4)] ![(1/8),1,(1/4)])) := by decide +kernel
#print axioms leaf00410_transform
theorem leaf00410_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00410=true := by decide +kernel
#print axioms leaf00410_sign
theorem leaf00410_log : RationalLog.accepts (5380063317/4294967296) (241867005/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00410_log
def leaf00410 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (92500484809/1000000000000) (5380063317/4294967296) (241867005/2147483648) 0 8 ![52,0,4] ![(3/4),0,(3/4)] ![(1/8),1,(1/4)] affine00410
theorem leaf00410_checked : FastNestedCellData.accepts 1 0 4 leaf00410=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (92500484809/1000000000000) (5380063317/4294967296) (241867005/2147483648) 0 8 ![52,0,4] ![(3/4),0,(3/4)] ![(1/8),1,(1/4)] 1706332769965681155534009401344000000000000 2335139850522862591123391850050272144392192 25244622829216360881823665881088000000000000 raw00410 affine00410
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00410_raw leaf00410_rectangular
    leaf00410_transform leaf00410_sign leaf00410_log
#print axioms leaf00410_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
