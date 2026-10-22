/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00030 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 11449732005186486882711130603520000000000 515229891515500516679294274590736384 6640724127765660033456537600000000000))
theorem leaf00030_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 11449732005186486882711130603520000000000 515229891515500516679294274590736384 6640724127765660033456537600000000000 raw00030=true := by decide +kernel
#print axioms leaf00030_raw
theorem leaf00030_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00030=true := by decide +kernel
#print axioms leaf00030_rectangular
def affine00030 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00030 (IntegerComputedClassCell.leftNumerator ![(1/320),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/320),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/320),0,0] ![(3/8000),1,(1/4)]))
theorem leaf00030_transform : affine00030=(NestedInteger.clearedAll 3 raw00030 (IntegerComputedClassCell.leftNumerator ![(1/320),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/320),0,0] ![(3/8000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/320),0,0] ![(3/8000),1,(1/4)])) := by decide +kernel
#print axioms leaf00030_transform
theorem leaf00030_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00030=true := by decide +kernel
#print axioms leaf00030_sign
theorem leaf00030_log : RationalLog.accepts (179355/4294967296) (-5413584905/1073741824) 15 8=true := by decide +kernel
#print axioms leaf00030_log
def leaf00030 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (15517280393/200000000000) (179355/4294967296) (-5413584905/1073741824) 15 8 ![52,0,4] ![(1/320),0,0] ![(3/8000),1,(1/4)] affine00030
theorem leaf00030_checked : FastNestedCellData.accepts 1 0 4 leaf00030=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (15517280393/200000000000) (179355/4294967296) (-5413584905/1073741824) 15 8 ![52,0,4] ![(1/320),0,0] ![(3/8000),1,(1/4)] 11449732005186486882711130603520000000000 515229891515500516679294274590736384 6640724127765660033456537600000000000 raw00030 affine00030
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00030_raw leaf00030_rectangular
    leaf00030_transform leaf00030_sign leaf00030_log
#print axioms leaf00030_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
