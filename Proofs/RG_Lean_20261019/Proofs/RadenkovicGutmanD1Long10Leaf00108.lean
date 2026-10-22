/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00108 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 963383138915417349310149715558400000000000 1705395568290498284696071693651069108224 6530941703652819267540221952000000000000))
theorem leaf00108_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 963383138915417349310149715558400000000000 1705395568290498284696071693651069108224 6530941703652819267540221952000000000000 raw00108=true := by decide +kernel
#print axioms leaf00108_raw
theorem leaf00108_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00108=true := by decide +kernel
#print axioms leaf00108_rectangular
def affine00108 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00108 (IntegerComputedClassCell.leftNumerator ![(37/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/3200),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00108_transform : affine00108=(NestedInteger.clearedAll 3 raw00108 (IntegerComputedClassCell.leftNumerator ![(37/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/3200),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00108_transform
theorem leaf00108_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00108=true := by decide +kernel
#print axioms leaf00108_sign
theorem leaf00108_log : RationalLog.accepts (6028755/4294967296) (-14106087497/4294967296) 10 8=true := by decide +kernel
#print axioms leaf00108_log
def leaf00108 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (261125523037/1000000000000) (6028755/4294967296) (-14106087497/4294967296) 10 8 ![52,0,4] ![(37/3200),0,0] ![(1/3200),1,(1/4)] affine00108
theorem leaf00108_checked : FastNestedCellData.accepts 1 0 4 leaf00108=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (261125523037/1000000000000) (6028755/4294967296) (-14106087497/4294967296) 10 8 ![52,0,4] ![(37/3200),0,0] ![(1/3200),1,(1/4)] 963383138915417349310149715558400000000000 1705395568290498284696071693651069108224 6530941703652819267540221952000000000000 raw00108 affine00108
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00108_raw leaf00108_rectangular
    leaf00108_transform leaf00108_sign leaf00108_log
#print axioms leaf00108_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
