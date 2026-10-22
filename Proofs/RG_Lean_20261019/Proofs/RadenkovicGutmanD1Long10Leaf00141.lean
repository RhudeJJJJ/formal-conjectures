/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00141 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2352322797853550925578927865856000000000000 13648175255442266965565031248390057361408 35675998809915193586872221696000000000000))
theorem leaf00141_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2352322797853550925578927865856000000000000 13648175255442266965565031248390057361408 35675998809915193586872221696000000000000 raw00141=true := by decide +kernel
#print axioms leaf00141_raw
theorem leaf00141_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00141=true := by decide +kernel
#print axioms leaf00141_rectangular
def affine00141 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00141 (IntegerComputedClassCell.leftNumerator ![(29/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/1600),0,0] ![(1/1600),1,(1/4)]))
theorem leaf00141_transform : affine00141=(NestedInteger.clearedAll 3 raw00141 (IntegerComputedClassCell.leftNumerator ![(29/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/1600),0,0] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00141_transform
theorem leaf00141_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00141=true := by decide +kernel
#print axioms leaf00141_sign
theorem leaf00141_log : RationalLog.accepts (18024111/4294967296) (-11754228103/4294967296) 8 8=true := by decide +kernel
#print axioms leaf00141_log
def leaf00141 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (382559023173/1000000000000) (18024111/4294967296) (-11754228103/4294967296) 8 8 ![52,0,4] ![(29/1600),0,0] ![(1/1600),1,(1/4)] affine00141
theorem leaf00141_checked : FastNestedCellData.accepts 1 0 4 leaf00141=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (382559023173/1000000000000) (18024111/4294967296) (-11754228103/4294967296) 8 8 ![52,0,4] ![(29/1600),0,0] ![(1/1600),1,(1/4)] 2352322797853550925578927865856000000000000 13648175255442266965565031248390057361408 35675998809915193586872221696000000000000 raw00141 affine00141
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00141_raw leaf00141_rectangular
    leaf00141_transform leaf00141_sign leaf00141_log
#print axioms leaf00141_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
