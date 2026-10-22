/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00429 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 179901396917466075794243584000000000000 164185643447952780332556020681805922304 4110175992635644810599858176000000000000))
theorem leaf00429_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 179901396917466075794243584000000000000 164185643447952780332556020681805922304 4110175992635644810599858176000000000000 raw00429=true := by decide +kernel
#print axioms leaf00429_raw
theorem leaf00429_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00429=true := by decide +kernel
#print axioms leaf00429_rectangular
def affine00429 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00429 (IntegerComputedClassCell.leftNumerator ![(69/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(69/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(69/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00429_transform : affine00429=(NestedInteger.clearedAll 3 raw00429 (IntegerComputedClassCell.leftNumerator ![(69/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(69/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(69/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00429_transform
theorem leaf00429_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00429=true := by decide +kernel
#print axioms leaf00429_sign
theorem leaf00429_log : RationalLog.accepts (235575259/268435456) (-70104647/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00429_log
def leaf00429 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9986533651/250000000000) (235575259/268435456) (-70104647/1073741824) 1 8 ![60,0,4] ![(69/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00429
theorem leaf00429_checked : FastNestedCellData.accepts 1 2 4 leaf00429=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9986533651/250000000000) (235575259/268435456) (-70104647/1073741824) 1 8 ![60,0,4] ![(69/6400),0,(1/2)] ![(1/6400),1,(1/2)] 179901396917466075794243584000000000000 164185643447952780332556020681805922304 4110175992635644810599858176000000000000 raw00429 affine00429
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00429_raw leaf00429_rectangular
    leaf00429_transform leaf00429_sign leaf00429_log
#print axioms leaf00429_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
