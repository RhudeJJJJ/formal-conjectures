/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01228 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 3492122013618839419086700544000000000000 3893202298101636963333379169720350015488 428445954805451021797958877184000000000000))
theorem leaf01228_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 3492122013618839419086700544000000000000 3893202298101636963333379169720350015488 428445954805451021797958877184000000000000 raw01228=true := by decide +kernel
#print axioms leaf01228_raw
theorem leaf01228_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01228=true := by decide +kernel
#print axioms leaf01228_rectangular
def affine01228 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01228 (IntegerComputedClassCell.leftNumerator ![(9/32),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/32),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/32),0,(7/8)] ![(1/64),1,(1/16)]))
theorem leaf01228_transform : affine01228=(NestedInteger.clearedAll 3 raw01228 (IntegerComputedClassCell.leftNumerator ![(9/32),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/32),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/32),0,(7/8)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01228_transform
theorem leaf01228_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01228=true := by decide +kernel
#print axioms leaf01228_sign
theorem leaf01228_log : RationalLog.accepts (1186284639/1073741824) (13378379/268435456) 0 8=true := by decide +kernel
#print axioms leaf01228_log
def leaf01228 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (9086799057/1000000000000) (1186284639/1073741824) (13378379/268435456) 0 8 ![60,0,4] ![(9/32),0,(7/8)] ![(1/64),1,(1/16)] affine01228
theorem leaf01228_checked : FastNestedCellData.accepts 1 2 4 leaf01228=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (9086799057/1000000000000) (1186284639/1073741824) (13378379/268435456) 0 8 ![60,0,4] ![(9/32),0,(7/8)] ![(1/64),1,(1/16)] 3492122013618839419086700544000000000000 3893202298101636963333379169720350015488 428445954805451021797958877184000000000000 raw01228 affine01228
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01228_raw leaf01228_rectangular
    leaf01228_transform leaf01228_sign leaf01228_log
#print axioms leaf01228_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
