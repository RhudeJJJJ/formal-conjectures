/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01249 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 89152887231732900406352674816000000000000 96070931460569627843325438168987611430912 19878165930505360465291496128512000000000000))
theorem leaf01249_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 89152887231732900406352674816000000000000 96070931460569627843325438168987611430912 19878165930505360465291496128512000000000000 raw01249=true := by decide +kernel
#print axioms leaf01249_raw
theorem leaf01249_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01249=true := by decide +kernel
#print axioms leaf01249_rectangular
def affine01249 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01249 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/32),0,(15/16)] ![(1/64),1,(1/16)]))
theorem leaf01249_transform : affine01249=(NestedInteger.clearedAll 3 raw01249 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/32),0,(15/16)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01249_transform
theorem leaf01249_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01249=true := by decide +kernel
#print axioms leaf01249_sign
theorem leaf01249_log : RationalLog.accepts (4605985497/4294967296) (150136405/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01249_log
def leaf01249 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (4832987701/1000000000000) (4605985497/4294967296) (150136405/4294967296) 0 8 ![60,0,4] ![(7/32),0,(15/16)] ![(1/64),1,(1/16)] affine01249
theorem leaf01249_checked : FastNestedCellData.accepts 1 2 4 leaf01249=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (4832987701/1000000000000) (4605985497/4294967296) (150136405/4294967296) 0 8 ![60,0,4] ![(7/32),0,(15/16)] ![(1/64),1,(1/16)] 89152887231732900406352674816000000000000 96070931460569627843325438168987611430912 19878165930505360465291496128512000000000000 raw01249 affine01249
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01249_raw leaf01249_rectangular
    leaf01249_transform leaf01249_sign leaf01249_log
#print axioms leaf01249_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
