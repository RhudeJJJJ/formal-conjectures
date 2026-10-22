/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00009 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3385978007989171104214994124800000000000 28001489494918502695713710876393472 635631602322710804299776000000000000))
theorem leaf00009_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3385978007989171104214994124800000000000 28001489494918502695713710876393472 635631602322710804299776000000000000 raw00009=true := by decide +kernel
#print axioms leaf00009_raw
theorem leaf00009_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00009=true := by decide +kernel
#print axioms leaf00009_rectangular
def affine00009 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00009 (IntegerComputedClassCell.leftNumerator ![(7/4000),0,0] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/4000),0,0] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/4000),0,0] ![(1/4000),1,(1/4)]))
theorem leaf00009_transform : affine00009=(NestedInteger.clearedAll 3 raw00009 (IntegerComputedClassCell.leftNumerator ![(7/4000),0,0] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/4000),0,0] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/4000),0,0] ![(1/4000),1,(1/4)])) := by decide +kernel
#print axioms leaf00009_transform
theorem leaf00009_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00009=true := by decide +kernel
#print axioms leaf00009_sign
theorem leaf00009_log : RationalLog.accepts (8505/1073741824) (-25224356225/4294967296) 17 8=true := by decide +kernel
#print axioms leaf00009_log
def leaf00009 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (44053016547/1000000000000) (8505/1073741824) (-25224356225/4294967296) 17 8 ![52,0,4] ![(7/4000),0,0] ![(1/4000),1,(1/4)] affine00009
theorem leaf00009_checked : FastNestedCellData.accepts 1 0 4 leaf00009=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (44053016547/1000000000000) (8505/1073741824) (-25224356225/4294967296) 17 8 ![52,0,4] ![(7/4000),0,0] ![(1/4000),1,(1/4)] 3385978007989171104214994124800000000000 28001489494918502695713710876393472 635631602322710804299776000000000000 raw00009 affine00009
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00009_raw leaf00009_rectangular
    leaf00009_transform leaf00009_sign leaf00009_log
#print axioms leaf00009_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
