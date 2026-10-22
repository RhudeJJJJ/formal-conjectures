/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00091 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 7117422021713086966363324416000000000000 6003102708441974940316909179910848774144 81034797264751347309249298432000000000000))
theorem leaf00091_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 7117422021713086966363324416000000000000 6003102708441974940316909179910848774144 81034797264751347309249298432000000000000 raw00091=true := by decide +kernel
#print axioms leaf00091_raw
theorem leaf00091_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00091=true := by decide +kernel
#print axioms leaf00091_rectangular
def affine00091 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00091 (IntegerComputedClassCell.leftNumerator ![(31/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/3200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00091_transform : affine00091=(NestedInteger.clearedAll 3 raw00091 (IntegerComputedClassCell.leftNumerator ![(31/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/3200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/3200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00091_transform
theorem leaf00091_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00091=true := by decide +kernel
#print axioms leaf00091_sign
theorem leaf00091_log : RationalLog.accepts (421585899/536870912) (-519120123/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00091_log
def leaf00091 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (74080554417/1000000000000) (421585899/536870912) (-519120123/4294967296) 1 8 ![52,0,4] ![(31/3200),0,(1/4)] ![(1/3200),1,(1/4)] affine00091
theorem leaf00091_checked : FastNestedCellData.accepts 1 0 4 leaf00091=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (74080554417/1000000000000) (421585899/536870912) (-519120123/4294967296) 1 8 ![52,0,4] ![(31/3200),0,(1/4)] ![(1/3200),1,(1/4)] 7117422021713086966363324416000000000000 6003102708441974940316909179910848774144 81034797264751347309249298432000000000000 raw00091 affine00091
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00091_raw leaf00091_rectangular
    leaf00091_transform leaf00091_sign leaf00091_log
#print axioms leaf00091_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
