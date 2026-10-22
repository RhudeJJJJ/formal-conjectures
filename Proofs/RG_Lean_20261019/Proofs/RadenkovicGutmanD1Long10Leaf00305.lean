/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00305 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 967850263297668809423581505126400000000000 633594136650378249935216518043394581200896 2415197748786030883525359566848000000000000))
theorem leaf00305_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 967850263297668809423581505126400000000000 633594136650378249935216518043394581200896 2415197748786030883525359566848000000000000 raw00305=true := by decide +kernel
#print axioms leaf00305_raw
theorem leaf00305_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00305=true := by decide +kernel
#print axioms leaf00305_rectangular
def affine00305 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00305 (IntegerComputedClassCell.leftNumerator ![(27/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(27/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(27/320),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00305_transform : affine00305=(NestedInteger.clearedAll 3 raw00305 (IntegerComputedClassCell.leftNumerator ![(27/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(27/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(27/320),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00305_transform
theorem leaf00305_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00305=true := by decide +kernel
#print axioms leaf00305_sign
theorem leaf00305_log : RationalLog.accepts (2227346345/4294967296) (-176263595/536870912) 1 8=true := by decide +kernel
#print axioms leaf00305_log
def leaf00305 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (262336339527/1000000000000) (2227346345/4294967296) (-176263595/536870912) 1 8 ![52,0,4] ![(27/320),0,(1/2)] ![(1/320),1,(1/2)] affine00305
theorem leaf00305_checked : FastNestedCellData.accepts 1 0 4 leaf00305=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (262336339527/1000000000000) (2227346345/4294967296) (-176263595/536870912) 1 8 ![52,0,4] ![(27/320),0,(1/2)] ![(1/320),1,(1/2)] 967850263297668809423581505126400000000000 633594136650378249935216518043394581200896 2415197748786030883525359566848000000000000 raw00305 affine00305
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00305_raw leaf00305_rectangular
    leaf00305_transform leaf00305_sign leaf00305_log
#print axioms leaf00305_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
