/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00242 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 90606048775292770370598207488000000000000 75653020203027338265353316076467806797824 962650894277942593821131931648000000000000))
theorem leaf00242_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 90606048775292770370598207488000000000000 75653020203027338265353316076467806797824 962650894277942593821131931648000000000000 raw00242=true := by decide +kernel
#print axioms leaf00242_raw
theorem leaf00242_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00242=true := by decide +kernel
#print axioms leaf00242_rectangular
def affine00242 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00242 (IntegerComputedClassCell.leftNumerator ![(1/200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/200),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00242_transform : affine00242=(NestedInteger.clearedAll 3 raw00242 (IntegerComputedClassCell.leftNumerator ![(1/200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/200),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00242_transform
theorem leaf00242_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00242=true := by decide +kernel
#print axioms leaf00242_sign
theorem leaf00242_log : RationalLog.accepts (1662429633/2147483648) (-137447871/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00242_log
def leaf00242 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (39294109969/500000000000) (1662429633/2147483648) (-137447871/1073741824) 1 8 ![60,0,4] ![(1/200),0,(1/8)] ![(1/6400),1,(1/8)] affine00242
theorem leaf00242_checked : FastNestedCellData.accepts 1 2 4 leaf00242=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (39294109969/500000000000) (1662429633/2147483648) (-137447871/1073741824) 1 8 ![60,0,4] ![(1/200),0,(1/8)] ![(1/6400),1,(1/8)] 90606048775292770370598207488000000000000 75653020203027338265353316076467806797824 962650894277942593821131931648000000000000 raw00242 affine00242
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00242_raw leaf00242_rectangular
    leaf00242_transform leaf00242_sign leaf00242_log
#print axioms leaf00242_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
