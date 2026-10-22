/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00920 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 955398757945994657878260056064000000000000 190971905571726914219550548341517300269056 230454158411034749204487471104000000000000))
theorem leaf00920_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 955398757945994657878260056064000000000000 190971905571726914219550548341517300269056 230454158411034749204487471104000000000000 raw00920=true := by decide +kernel
#print axioms leaf00920_raw
theorem leaf00920_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00920=true := by decide +kernel
#print axioms leaf00920_rectangular
def affine00920 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00920 (IntegerComputedClassCell.leftNumerator ![(5/64),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/64),0,0] ![(1/320),1,(1/16)]))
theorem leaf00920_transform : affine00920=(NestedInteger.clearedAll 3 raw00920 (IntegerComputedClassCell.leftNumerator ![(5/64),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/64),0,0] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00920_transform
theorem leaf00920_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00920=true := by decide +kernel
#print axioms leaf00920_sign
theorem leaf00920_log : RationalLog.accepts (469469981/4294967296) (-2376829455/2147483648) 4 8=true := by decide +kernel
#print axioms leaf00920_log
def leaf00920 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (207169081791/250000000000) (469469981/4294967296) (-2376829455/2147483648) 4 8 ![60,0,4] ![(5/64),0,0] ![(1/320),1,(1/16)] affine00920
theorem leaf00920_checked : FastNestedCellData.accepts 1 2 4 leaf00920=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (207169081791/250000000000) (469469981/4294967296) (-2376829455/2147483648) 4 8 ![60,0,4] ![(5/64),0,0] ![(1/320),1,(1/16)] 955398757945994657878260056064000000000000 190971905571726914219550548341517300269056 230454158411034749204487471104000000000000 raw00920 affine00920
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00920_raw leaf00920_rectangular
    leaf00920_transform leaf00920_sign leaf00920_log
#print axioms leaf00920_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
