/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00071 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 221211750511601736831852557107200000000000 192575325308418884962144693022541886783488 3211753202675782378314035888128000000000000))
theorem leaf00071_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 221211750511601736831852557107200000000000 192575325308418884962144693022541886783488 3211753202675782378314035888128000000000000 raw00071=true := by decide +kernel
#print axioms leaf00071_raw
theorem leaf00071_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00071=true := by decide +kernel
#print axioms leaf00071_rectangular
def affine00071 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00071 (IntegerComputedClassCell.leftNumerator ![(3/1600),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/1600),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/1600),0,(1/16)] ![(1/16000),1,(1/16)]))
theorem leaf00071_transform : affine00071=(NestedInteger.clearedAll 3 raw00071 (IntegerComputedClassCell.leftNumerator ![(3/1600),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/1600),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/1600),0,(1/16)] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00071_transform
theorem leaf00071_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00071=true := by decide +kernel
#print axioms leaf00071_sign
theorem leaf00071_log : RationalLog.accepts (3527467415/4294967296) (-422761771/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00071_log
def leaf00071 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (59959565121/1000000000000) (3527467415/4294967296) (-422761771/4294967296) 1 8 ![60,0,4] ![(3/1600),0,(1/16)] ![(1/16000),1,(1/16)] affine00071
theorem leaf00071_checked : FastNestedCellData.accepts 1 2 4 leaf00071=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (59959565121/1000000000000) (3527467415/4294967296) (-422761771/4294967296) 1 8 ![60,0,4] ![(3/1600),0,(1/16)] ![(1/16000),1,(1/16)] 221211750511601736831852557107200000000000 192575325308418884962144693022541886783488 3211753202675782378314035888128000000000000 raw00071 affine00071
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00071_raw leaf00071_rectangular
    leaf00071_transform leaf00071_sign leaf00071_log
#print axioms leaf00071_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
