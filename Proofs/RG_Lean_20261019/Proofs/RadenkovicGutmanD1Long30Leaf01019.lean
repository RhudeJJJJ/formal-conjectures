/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01019 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1586196502251514180650227728384000000000000 1171877006074898752101000362275246908112896 3407099181318976287982303051776000000000000))
theorem leaf01019_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1586196502251514180650227728384000000000000 1171877006074898752101000362275246908112896 3407099181318976287982303051776000000000000 raw01019=true := by decide +kernel
#print axioms leaf01019_raw
theorem leaf01019_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01019=true := by decide +kernel
#print axioms leaf01019_rectangular
def affine01019 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01019 (IntegerComputedClassCell.leftNumerator ![(7/40),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/40),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/40),0,(1/2)] ![(1/80),1,(1/2)]))
theorem leaf01019_transform : affine01019=(NestedInteger.clearedAll 3 raw01019 (IntegerComputedClassCell.leftNumerator ![(7/40),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/40),0,(1/2)] ![(1/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/40),0,(1/2)] ![(1/80),1,(1/2)])) := by decide +kernel
#print axioms leaf01019_transform
theorem leaf01019_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01019=true := by decide +kernel
#print axioms leaf01019_sign
theorem leaf01019_log : RationalLog.accepts (2361028869/4294967296) (-1284939265/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01019_log
def leaf01019 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (171975769373/500000000000) (2361028869/4294967296) (-1284939265/4294967296) 1 8 ![60,0,4] ![(7/40),0,(1/2)] ![(1/80),1,(1/2)] affine01019
theorem leaf01019_checked : FastNestedCellData.accepts 1 2 4 leaf01019=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (171975769373/500000000000) (2361028869/4294967296) (-1284939265/4294967296) 1 8 ![60,0,4] ![(7/40),0,(1/2)] ![(1/80),1,(1/2)] 1586196502251514180650227728384000000000000 1171877006074898752101000362275246908112896 3407099181318976287982303051776000000000000 raw01019 affine01019
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01019_raw leaf01019_rectangular
    leaf01019_transform leaf01019_sign leaf01019_log
#print axioms leaf01019_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
