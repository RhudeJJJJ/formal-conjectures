/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01133 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 95548007545599178781237528494080000000000 119999338157729238143734343073999467053056 926695233892238619848210382848000000000000))
theorem leaf01133_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 95548007545599178781237528494080000000000 119999338157729238143734343073999467053056 926695233892238619848210382848000000000000 raw01133=true := by decide +kernel
#print axioms leaf01133_raw
theorem leaf01133_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01133=true := by decide +kernel
#print axioms leaf01133_rectangular
def affine01133 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01133 (IntegerComputedClassCell.leftNumerator ![(13/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/16),0,(7/8)] ![(1/16),1,(1/16)]))
theorem leaf01133_transform : affine01133=(NestedInteger.clearedAll 3 raw01133 (IntegerComputedClassCell.leftNumerator ![(13/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/16),0,(7/8)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01133_transform
theorem leaf01133_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01133=true := by decide +kernel
#print axioms leaf01133_sign
theorem leaf01133_log : RationalLog.accepts (4775666975/4294967296) (14239119/268435456) 0 8=true := by decide +kernel
#print axioms leaf01133_log
def leaf01133 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (129491696697/1000000000000) (4775666975/4294967296) (14239119/268435456) 0 8 ![60,0,4] ![(13/16),0,(7/8)] ![(1/16),1,(1/16)] affine01133
theorem leaf01133_checked : FastNestedCellData.accepts 1 2 4 leaf01133=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (129491696697/1000000000000) (4775666975/4294967296) (14239119/268435456) 0 8 ![60,0,4] ![(13/16),0,(7/8)] ![(1/16),1,(1/16)] 95548007545599178781237528494080000000000 119999338157729238143734343073999467053056 926695233892238619848210382848000000000000 raw01133 affine01133
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01133_raw leaf01133_rectangular
    leaf01133_transform leaf01133_sign leaf01133_log
#print axioms leaf01133_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
