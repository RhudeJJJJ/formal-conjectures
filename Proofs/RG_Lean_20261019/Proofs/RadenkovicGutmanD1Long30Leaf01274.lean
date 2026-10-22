/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01274 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 12002065985344607617024000000000000 12667480048978318576280057166168064 4641881364584831798738944000000000000))
theorem leaf01274_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 12002065985344607617024000000000000 12667480048978318576280057166168064 4641881364584831798738944000000000000 raw01274=true := by decide +kernel
#print axioms leaf01274_raw
theorem leaf01274_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01274=true := by decide +kernel
#print axioms leaf01274_rectangular
def affine01274 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01274 (IntegerComputedClassCell.leftNumerator ![(23/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/128),0,(15/16)] ![(1/128),1,(1/16)]))
theorem leaf01274_transform : affine01274=(NestedInteger.clearedAll 3 raw01274 (IntegerComputedClassCell.leftNumerator ![(23/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/128),0,(15/16)] ![(1/128),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/128),0,(15/16)] ![(1/128),1,(1/16)])) := by decide +kernel
#print axioms leaf01274_transform
theorem leaf01274_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01274=true := by decide +kernel
#print axioms leaf01274_sign
theorem leaf01274_log : RationalLog.accepts (4520750351/4294967296) (110024275/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01274_log
def leaf01274 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1332497/488281250) (4520750351/4294967296) (110024275/4294967296) 0 8 ![60,0,4] ![(23/128),0,(15/16)] ![(1/128),1,(1/16)] affine01274
theorem leaf01274_checked : FastNestedCellData.accepts 1 2 4 leaf01274=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1332497/488281250) (4520750351/4294967296) (110024275/4294967296) 0 8 ![60,0,4] ![(23/128),0,(15/16)] ![(1/128),1,(1/16)] 12002065985344607617024000000000000 12667480048978318576280057166168064 4641881364584831798738944000000000000 raw01274 affine01274
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01274_raw leaf01274_rectangular
    leaf01274_transform leaf01274_sign leaf01274_log
#print axioms leaf01274_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
