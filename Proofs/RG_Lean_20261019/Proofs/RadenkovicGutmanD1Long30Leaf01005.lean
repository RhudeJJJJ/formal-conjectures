/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01005 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11990842981781438973964686721024000000000000 6532480507563492478293023207124393768517632 10049585026891686993526561701888000000000000))
theorem leaf01005_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11990842981781438973964686721024000000000000 6532480507563492478293023207124393768517632 10049585026891686993526561701888000000000000 raw01005=true := by decide +kernel
#print axioms leaf01005_raw
theorem leaf01005_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01005=true := by decide +kernel
#print axioms leaf01005_rectangular
def affine01005 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01005 (IntegerComputedClassCell.leftNumerator ![(5/32),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/32),0,0] ![(1/160),1,(1/16)]))
theorem leaf01005_transform : affine01005=(NestedInteger.clearedAll 3 raw01005 (IntegerComputedClassCell.leftNumerator ![(5/32),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(5/32),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(5/32),0,0] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01005_transform
theorem leaf01005_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01005=true := by decide +kernel
#print axioms leaf01005_sign
theorem leaf01005_log : RationalLog.accepts (1418070327/4294967296) (-2379727457/4294967296) 2 8=true := by decide +kernel
#print axioms leaf01005_log
def leaf01005 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (650024900539/1000000000000) (1418070327/4294967296) (-2379727457/4294967296) 2 8 ![60,0,4] ![(5/32),0,0] ![(1/160),1,(1/16)] affine01005
theorem leaf01005_checked : FastNestedCellData.accepts 1 2 4 leaf01005=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (650024900539/1000000000000) (1418070327/4294967296) (-2379727457/4294967296) 2 8 ![60,0,4] ![(5/32),0,0] ![(1/160),1,(1/16)] 11990842981781438973964686721024000000000000 6532480507563492478293023207124393768517632 10049585026891686993526561701888000000000000 raw01005 affine01005
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01005_raw leaf01005_rectangular
    leaf01005_transform leaf01005_sign leaf01005_log
#print axioms leaf01005_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
