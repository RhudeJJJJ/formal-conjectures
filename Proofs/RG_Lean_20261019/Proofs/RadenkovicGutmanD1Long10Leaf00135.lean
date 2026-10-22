/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00135 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 34776660979946622809626640384000000000000 168067715794934944740477242510917238784 464317347492201518017282048000000000000))
theorem leaf00135_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 34776660979946622809626640384000000000000 168067715794934944740477242510917238784 464317347492201518017282048000000000000 raw00135=true := by decide +kernel
#print axioms leaf00135_raw
theorem leaf00135_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00135=true := by decide +kernel
#print axioms leaf00135_rectangular
def affine00135 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00135 (IntegerComputedClassCell.leftNumerator ![(27/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/1600),0,0] ![(1/1600),1,(1/4)]))
theorem leaf00135_transform : affine00135=(NestedInteger.clearedAll 3 raw00135 (IntegerComputedClassCell.leftNumerator ![(27/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/1600),0,0] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00135_transform
theorem leaf00135_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00135=true := by decide +kernel
#print axioms leaf00135_sign
theorem leaf00135_log : RationalLog.accepts (7620081/2147483648) (-12114524745/4294967296) 9 8=true := by decide +kernel
#print axioms leaf00135_log
def leaf00135 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (90491835327/250000000000) (7620081/2147483648) (-12114524745/4294967296) 9 8 ![52,0,4] ![(27/1600),0,0] ![(1/1600),1,(1/4)] affine00135
theorem leaf00135_checked : FastNestedCellData.accepts 1 0 4 leaf00135=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (90491835327/250000000000) (7620081/2147483648) (-12114524745/4294967296) 9 8 ![52,0,4] ![(27/1600),0,0] ![(1/1600),1,(1/4)] 34776660979946622809626640384000000000000 168067715794934944740477242510917238784 464317347492201518017282048000000000000 raw00135 affine00135
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00135_raw leaf00135_rectangular
    leaf00135_transform leaf00135_sign leaf00135_log
#print axioms leaf00135_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
