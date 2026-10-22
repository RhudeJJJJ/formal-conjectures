/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00732 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7537056416264701681984054755328000000000000 3341256385833352277316582082869861480923136 8177635674997573513920267681792000000000000))
theorem leaf00732_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7537056416264701681984054755328000000000000 3341256385833352277316582082869861480923136 8177635674997573513920267681792000000000000 raw00732=true := by decide +kernel
#print axioms leaf00732_raw
theorem leaf00732_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00732=true := by decide +kernel
#print axioms leaf00732_rectangular
def affine00732 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00732 (IntegerComputedClassCell.leftNumerator ![(203/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(203/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(203/6400),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00732_transform : affine00732=(NestedInteger.clearedAll 3 raw00732 (IntegerComputedClassCell.leftNumerator ![(203/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(203/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(203/6400),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00732_transform
theorem leaf00732_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00732=true := by decide +kernel
#print axioms leaf00732_sign
theorem leaf00732_log : RationalLog.accepts (1351714419/4294967296) (-77582561/134217728) 2 8=true := by decide +kernel
#print axioms leaf00732_log
def leaf00732 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (408584647033/1000000000000) (1351714419/4294967296) (-77582561/134217728) 2 8 ![60,0,4] ![(203/6400),0,(1/8)] ![(3/6400),1,(1/8)] affine00732
theorem leaf00732_checked : FastNestedCellData.accepts 1 2 4 leaf00732=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (408584647033/1000000000000) (1351714419/4294967296) (-77582561/134217728) 2 8 ![60,0,4] ![(203/6400),0,(1/8)] ![(3/6400),1,(1/8)] 7537056416264701681984054755328000000000000 3341256385833352277316582082869861480923136 8177635674997573513920267681792000000000000 raw00732 affine00732
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00732_raw leaf00732_rectangular
    leaf00732_transform leaf00732_sign leaf00732_log
#print axioms leaf00732_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
