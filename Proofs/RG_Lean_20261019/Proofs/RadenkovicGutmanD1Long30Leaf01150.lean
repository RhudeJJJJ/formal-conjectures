/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01150 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1661220621916878084057866436608000000000000 2130341951328994868408534606851220717961216 23656022714374486056464371679232000000000000))
theorem leaf01150_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1661220621916878084057866436608000000000000 2130341951328994868408534606851220717961216 23656022714374486056464371679232000000000000 raw01150=true := by decide +kernel
#print axioms leaf01150_raw
theorem leaf01150_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01150=true := by decide +kernel
#print axioms leaf01150_rectangular
def affine01150 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01150 (IntegerComputedClassCell.leftNumerator ![(7/8),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/8),0,0] ![(1/16),1,(1/2)]))
theorem leaf01150_transform : affine01150=(NestedInteger.clearedAll 3 raw01150 (IntegerComputedClassCell.leftNumerator ![(7/8),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/8),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf01150_transform
theorem leaf01150_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01150=true := by decide +kernel
#print axioms leaf01150_sign
theorem leaf01150_log : RationalLog.accepts (5052815909/4294967296) (2726327/33554432) 0 8=true := by decide +kernel
#print axioms leaf01150_log
def leaf01150 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (90054950363/1000000000000) (5052815909/4294967296) (2726327/33554432) 0 8 ![60,0,4] ![(7/8),0,0] ![(1/16),1,(1/2)] affine01150
theorem leaf01150_checked : FastNestedCellData.accepts 1 2 4 leaf01150=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (90054950363/1000000000000) (5052815909/4294967296) (2726327/33554432) 0 8 ![60,0,4] ![(7/8),0,0] ![(1/16),1,(1/2)] 1661220621916878084057866436608000000000000 2130341951328994868408534606851220717961216 23656022714374486056464371679232000000000000 raw01150 affine01150
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01150_raw leaf01150_rectangular
    leaf01150_transform leaf01150_sign leaf01150_log
#print axioms leaf01150_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
