/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00212 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 471708176455288994545001929113600000000000 360692866856055207617653260171700271579136 2821070032792577272598843359232000000000000))
theorem leaf00212_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 471708176455288994545001929113600000000000 360692866856055207617653260171700271579136 2821070032792577272598843359232000000000000 raw00212=true := by decide +kernel
#print axioms leaf00212_raw
theorem leaf00212_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00212=true := by decide +kernel
#print axioms leaf00212_rectangular
def affine00212 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00212 (IntegerComputedClassCell.leftNumerator ![(23/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/640),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00212_transform : affine00212=(NestedInteger.clearedAll 3 raw00212 (IntegerComputedClassCell.leftNumerator ![(23/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/640),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00212_transform
theorem leaf00212_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00212=true := by decide +kernel
#print axioms leaf00212_sign
theorem leaf00212_log : RationalLog.accepts (2911857145/4294967296) (-834625717/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00212_log
def leaf00212 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (127856757423/1000000000000) (2911857145/4294967296) (-834625717/4294967296) 1 8 ![52,0,4] ![(23/640),0,(1/2)] ![(3/3200),1,(1/2)] affine00212
theorem leaf00212_checked : FastNestedCellData.accepts 1 0 4 leaf00212=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (127856757423/1000000000000) (2911857145/4294967296) (-834625717/4294967296) 1 8 ![52,0,4] ![(23/640),0,(1/2)] ![(3/3200),1,(1/2)] 471708176455288994545001929113600000000000 360692866856055207617653260171700271579136 2821070032792577272598843359232000000000000 raw00212 affine00212
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00212_raw leaf00212_rectangular
    leaf00212_transform leaf00212_sign leaf00212_log
#print axioms leaf00212_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
