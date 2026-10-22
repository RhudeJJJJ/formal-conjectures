/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00345 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 746025222982168538176253067264000000000000 330869920369709349995732700910956161531904 511332639527806902189200244736000000000000))
theorem leaf00345_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 746025222982168538176253067264000000000000 330869920369709349995732700910956161531904 511332639527806902189200244736000000000000 raw00345=true := by decide +kernel
#print axioms leaf00345_raw
theorem leaf00345_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00345=true := by decide +kernel
#print axioms leaf00345_rectangular
def affine00345 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00345 (IntegerComputedClassCell.leftNumerator ![(3/20),0,0] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/20),0,0] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/20),0,0] ![(1/80),1,(1/4)]))
theorem leaf00345_transform : affine00345=(NestedInteger.clearedAll 3 raw00345 (IntegerComputedClassCell.leftNumerator ![(3/20),0,0] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/20),0,0] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/20),0,0] ![(1/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00345_transform
theorem leaf00345_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00345=true := by decide +kernel
#print axioms leaf00345_sign
theorem leaf00345_log : RationalLog.accepts (289128301/1073741824) (-2817572321/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00345_log
def leaf00345 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (647073733989/1000000000000) (289128301/1073741824) (-2817572321/4294967296) 2 8 ![52,0,4] ![(3/20),0,0] ![(1/80),1,(1/4)] affine00345
theorem leaf00345_checked : FastNestedCellData.accepts 1 0 4 leaf00345=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (647073733989/1000000000000) (289128301/1073741824) (-2817572321/4294967296) 2 8 ![52,0,4] ![(3/20),0,0] ![(1/80),1,(1/4)] 746025222982168538176253067264000000000000 330869920369709349995732700910956161531904 511332639527806902189200244736000000000000 raw00345 affine00345
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00345_raw leaf00345_rectangular
    leaf00345_transform leaf00345_sign leaf00345_log
#print axioms leaf00345_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
