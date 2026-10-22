/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00300 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 99802755606862333076663644979200000000000 134053139106678936372307930828828049408 247773113511934097587856998400000000000))
theorem leaf00300_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 99802755606862333076663644979200000000000 134053139106678936372307930828828049408 247773113511934097587856998400000000000 raw00300=true := by decide +kernel
#print axioms leaf00300_raw
theorem leaf00300_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00300=true := by decide +kernel
#print axioms leaf00300_rectangular
def affine00300 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00300 (IntegerComputedClassCell.leftNumerator ![(11/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/1600),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00300_transform : affine00300=(NestedInteger.clearedAll 3 raw00300 (IntegerComputedClassCell.leftNumerator ![(11/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/1600),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00300_transform
theorem leaf00300_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00300=true := by decide +kernel
#print axioms leaf00300_sign
theorem leaf00300_log : RationalLog.accepts (1871771/2147483648) (-7564690657/2147483648) 11 8=true := by decide +kernel
#print axioms leaf00300_log
def leaf00300 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (108206364449/200000000000) (1871771/2147483648) (-7564690657/2147483648) 11 8 ![60,0,4] ![(11/1600),0,0] ![(1/6400),1,(1/16)] affine00300
theorem leaf00300_checked : FastNestedCellData.accepts 1 2 4 leaf00300=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (108206364449/200000000000) (1871771/2147483648) (-7564690657/2147483648) 11 8 ![60,0,4] ![(11/1600),0,0] ![(1/6400),1,(1/16)] 99802755606862333076663644979200000000000 134053139106678936372307930828828049408 247773113511934097587856998400000000000 raw00300 affine00300
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00300_raw leaf00300_rectangular
    leaf00300_transform leaf00300_sign leaf00300_log
#print axioms leaf00300_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
