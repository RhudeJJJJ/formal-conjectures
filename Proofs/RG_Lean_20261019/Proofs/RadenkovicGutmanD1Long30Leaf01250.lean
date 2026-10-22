/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01250 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 257757038393811495669255372800000000000 276541243964158050304065851785054519296 65970206995707744223976908390400000000000))
theorem leaf01250_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 257757038393811495669255372800000000000 276541243964158050304065851785054519296 65970206995707744223976908390400000000000 raw01250=true := by decide +kernel
#print axioms leaf01250_raw
theorem leaf01250_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01250=true := by decide +kernel
#print axioms leaf01250_rectangular
def affine01250 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01250 (IntegerComputedClassCell.leftNumerator ![(27/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(27/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(27/128),0,0] ![(1/128),1,(1/2)]))
theorem leaf01250_transform : affine01250=(NestedInteger.clearedAll 3 raw01250 (IntegerComputedClassCell.leftNumerator ![(27/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(27/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(27/128),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf01250_transform
theorem leaf01250_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01250=true := by decide +kernel
#print axioms leaf01250_sign
theorem leaf01250_log : RationalLog.accepts (2294365089/2147483648) (142076219/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01250_log
def leaf01250 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (838382223/200000000000) (2294365089/2147483648) (142076219/4294967296) 0 8 ![60,0,4] ![(27/128),0,0] ![(1/128),1,(1/2)] affine01250
theorem leaf01250_checked : FastNestedCellData.accepts 1 2 4 leaf01250=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (838382223/200000000000) (2294365089/2147483648) (142076219/4294967296) 0 8 ![60,0,4] ![(27/128),0,0] ![(1/128),1,(1/2)] 257757038393811495669255372800000000000 276541243964158050304065851785054519296 65970206995707744223976908390400000000000 raw01250 affine01250
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01250_raw leaf01250_rectangular
    leaf01250_transform leaf01250_sign leaf01250_log
#print axioms leaf01250_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
