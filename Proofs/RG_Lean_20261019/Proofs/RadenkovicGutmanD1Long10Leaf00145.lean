/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00145 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 162283433374002384428878266368000000000000 119036575965045635619809811369826015248384 845679841814668626729671589888000000000000))
theorem leaf00145_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 162283433374002384428878266368000000000000 119036575965045635619809811369826015248384 845679841814668626729671589888000000000000 raw00145=true := by decide +kernel
#print axioms leaf00145_raw
theorem leaf00145_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00145=true := by decide +kernel
#print axioms leaf00145_rectangular
def affine00145 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00145 (IntegerComputedClassCell.leftNumerator ![(3/160),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/160),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/160),0,(1/4)] ![(1/1600),1,(1/4)]))
theorem leaf00145_transform : affine00145=(NestedInteger.clearedAll 3 raw00145 (IntegerComputedClassCell.leftNumerator ![(3/160),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/160),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/160),0,(1/4)] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00145_transform
theorem leaf00145_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00145=true := by decide +kernel
#print axioms leaf00145_sign
theorem leaf00145_log : RationalLog.accepts (1380836993/2147483648) (-948343693/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00145_log
def leaf00145 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (70379220409/500000000000) (1380836993/2147483648) (-948343693/4294967296) 1 8 ![52,0,4] ![(3/160),0,(1/4)] ![(1/1600),1,(1/4)] affine00145
theorem leaf00145_checked : FastNestedCellData.accepts 1 0 4 leaf00145=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (70379220409/500000000000) (1380836993/2147483648) (-948343693/4294967296) 1 8 ![52,0,4] ![(3/160),0,(1/4)] ![(1/1600),1,(1/4)] 162283433374002384428878266368000000000000 119036575965045635619809811369826015248384 845679841814668626729671589888000000000000 raw00145 affine00145
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00145_raw leaf00145_rectangular
    leaf00145_transform leaf00145_sign leaf00145_log
#print axioms leaf00145_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
