/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00462 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 28307624941980398997437677568000000000000 29341737041590602565016048285270711205888 19120626156156745039267240083456000000000000))
theorem leaf00462_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 28307624941980398997437677568000000000000 29341737041590602565016048285270711205888 19120626156156745039267240083456000000000000 raw00462=true := by decide +kernel
#print axioms leaf00462_raw
theorem leaf00462_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00462=true := by decide +kernel
#print axioms leaf00462_rectangular
def affine00462 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00462 (IntegerComputedClassCell.leftNumerator ![(9/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/64),0,0] ![(1/64),1,(1/2)]))
theorem leaf00462_transform : affine00462=(NestedInteger.clearedAll 3 raw00462 (IntegerComputedClassCell.leftNumerator ![(9/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/64),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf00462_transform
theorem leaf00462_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00462=true := by decide +kernel
#print axioms leaf00462_sign
theorem leaf00462_log : RationalLog.accepts (4445046507/4294967296) (9219789/536870912) 0 8=true := by decide +kernel
#print axioms leaf00462_log
def leaf00462 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (1534559423/1000000000000) (4445046507/4294967296) (9219789/536870912) 0 8 ![52,0,4] ![(9/64),0,0] ![(1/64),1,(1/2)] affine00462
theorem leaf00462_checked : FastNestedCellData.accepts 1 0 4 leaf00462=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (1534559423/1000000000000) (4445046507/4294967296) (9219789/536870912) 0 8 ![52,0,4] ![(9/64),0,0] ![(1/64),1,(1/2)] 28307624941980398997437677568000000000000 29341737041590602565016048285270711205888 19120626156156745039267240083456000000000000 raw00462 affine00462
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00462_raw leaf00462_rectangular
    leaf00462_transform leaf00462_sign leaf00462_log
#print axioms leaf00462_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
