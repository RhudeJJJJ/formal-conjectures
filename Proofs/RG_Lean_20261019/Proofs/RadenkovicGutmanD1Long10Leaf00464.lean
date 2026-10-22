/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00464 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 28307624868193422702599471104000000000000 29341736964990910823123689529161015099392 19120626156080379721760183943168000000000000))
theorem leaf00464_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 28307624868193422702599471104000000000000 29341736964990910823123689529161015099392 19120626156080379721760183943168000000000000 raw00464=true := by decide +kernel
#print axioms leaf00464_raw
theorem leaf00464_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00464=true := by decide +kernel
#print axioms leaf00464_rectangular
def affine00464 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00464 (IntegerComputedClassCell.leftNumerator ![(9/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/64),0,(3/4)] ![(1/64),1,(1/4)]))
theorem leaf00464_transform : affine00464=(NestedInteger.clearedAll 3 raw00464 (IntegerComputedClassCell.leftNumerator ![(9/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/64),0,(3/4)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00464_transform
theorem leaf00464_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00464=true := by decide +kernel
#print axioms leaf00464_sign
theorem leaf00464_log : RationalLog.accepts (4445046507/4294967296) (9219789/536870912) 0 8=true := by decide +kernel
#print axioms leaf00464_log
def leaf00464 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (1534559419/1000000000000) (4445046507/4294967296) (9219789/536870912) 0 8 ![52,0,4] ![(9/64),0,(3/4)] ![(1/64),1,(1/4)] affine00464
theorem leaf00464_checked : FastNestedCellData.accepts 1 0 4 leaf00464=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (1534559419/1000000000000) (4445046507/4294967296) (9219789/536870912) 0 8 ![52,0,4] ![(9/64),0,(3/4)] ![(1/64),1,(1/4)] 28307624868193422702599471104000000000000 29341736964990910823123689529161015099392 19120626156080379721760183943168000000000000 raw00464 affine00464
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00464_raw leaf00464_rectangular
    leaf00464_transform leaf00464_sign leaf00464_log
#print axioms leaf00464_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
