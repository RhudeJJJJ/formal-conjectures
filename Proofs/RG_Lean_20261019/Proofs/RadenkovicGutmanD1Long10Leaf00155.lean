/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00155 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1372930520188476568431312764928000000000000 1161680060060448739617074311162736802791424 15608375258876775326956207996928000000000000))
theorem leaf00155_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1372930520188476568431312764928000000000000 1161680060060448739617074311162736802791424 15608375258876775326956207996928000000000000 raw00155=true := by decide +kernel
#print axioms leaf00155_raw
theorem leaf00155_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00155=true := by decide +kernel
#print axioms leaf00155_rectangular
def affine00155 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00155 (IntegerComputedClassCell.leftNumerator ![(131/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(131/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(131/6400),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00155_transform : affine00155=(NestedInteger.clearedAll 3 raw00155 (IntegerComputedClassCell.leftNumerator ![(131/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(131/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(131/6400),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00155_transform
theorem leaf00155_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00155=true := by decide +kernel
#print axioms leaf00155_sign
theorem leaf00155_log : RationalLog.accepts (3382369421/4294967296) (-512964011/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00155_log
def leaf00155 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (74426712633/1000000000000) (3382369421/4294967296) (-512964011/4294967296) 1 8 ![52,0,4] ![(131/6400),0,(1/2)] ![(3/6400),1,(1/2)] affine00155
theorem leaf00155_checked : FastNestedCellData.accepts 1 0 4 leaf00155=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (74426712633/1000000000000) (3382369421/4294967296) (-512964011/4294967296) 1 8 ![52,0,4] ![(131/6400),0,(1/2)] ![(3/6400),1,(1/2)] 1372930520188476568431312764928000000000000 1161680060060448739617074311162736802791424 15608375258876775326956207996928000000000000 raw00155 affine00155
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00155_raw leaf00155_rectangular
    leaf00155_transform leaf00155_sign leaf00155_log
#print axioms leaf00155_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
