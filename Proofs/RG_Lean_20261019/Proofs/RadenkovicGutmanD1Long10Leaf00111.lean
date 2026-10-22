/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00111 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 4988573367438361404368396222464000000000000 9575253500160274739381032122373508169728 35407367547457574723945234432000000000000))
theorem leaf00111_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 4988573367438361404368396222464000000000000 9575253500160274739381032122373508169728 35407367547457574723945234432000000000000 raw00111=true := by decide +kernel
#print axioms leaf00111_raw
theorem leaf00111_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00111=true := by decide +kernel
#print axioms leaf00111_rectangular
def affine00111 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00111 (IntegerComputedClassCell.leftNumerator ![(19/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/1600),0,0] ![(1/1600),1,(1/4)]))
theorem leaf00111_transform : affine00111=(NestedInteger.clearedAll 3 raw00111 (IntegerComputedClassCell.leftNumerator ![(19/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/1600),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/1600),0,0] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00111_transform
theorem leaf00111_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00111=true := by decide +kernel
#print axioms leaf00111_sign
theorem leaf00111_log : RationalLog.accepts (6489073/4294967296) (-6974038723/2147483648) 10 8=true := by decide +kernel
#print axioms leaf00111_log
def leaf00111 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (270431104129/1000000000000) (6489073/4294967296) (-6974038723/2147483648) 10 8 ![52,0,4] ![(19/1600),0,0] ![(1/1600),1,(1/4)] affine00111
theorem leaf00111_checked : FastNestedCellData.accepts 1 0 4 leaf00111=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (270431104129/1000000000000) (6489073/4294967296) (-6974038723/2147483648) 10 8 ![52,0,4] ![(19/1600),0,0] ![(1/1600),1,(1/4)] 4988573367438361404368396222464000000000000 9575253500160274739381032122373508169728 35407367547457574723945234432000000000000 raw00111 affine00111
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00111_raw leaf00111_rectangular
    leaf00111_transform leaf00111_sign leaf00111_log
#print axioms leaf00111_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
