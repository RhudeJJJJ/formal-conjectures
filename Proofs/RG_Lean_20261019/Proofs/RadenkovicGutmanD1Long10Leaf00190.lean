/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00190 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 196083080657950199076638792089600000000000 125916818440364099846293814807484514172928 592288563743291995488144850944000000000000))
theorem leaf00190_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 196083080657950199076638792089600000000000 125916818440364099846293814807484514172928 592288563743291995488144850944000000000000 raw00190=true := by decide +kernel
#print axioms leaf00190_raw
theorem leaf00190_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00190=true := by decide +kernel
#print axioms leaf00190_rectangular
def affine00190 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00190 (IntegerComputedClassCell.leftNumerator ![(47/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/1600),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00190_transform : affine00190=(NestedInteger.clearedAll 3 raw00190 (IntegerComputedClassCell.leftNumerator ![(47/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/1600),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00190_transform
theorem leaf00190_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00190=true := by decide +kernel
#print axioms leaf00190_sign
theorem leaf00190_log : RationalLog.accepts (1137255845/2147483648) (-682554667/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00190_log
def leaf00190 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (212593702037/1000000000000) (1137255845/2147483648) (-682554667/2147483648) 1 8 ![52,0,4] ![(47/1600),0,(1/4)] ![(3/3200),1,(1/4)] affine00190
theorem leaf00190_checked : FastNestedCellData.accepts 1 0 4 leaf00190=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (212593702037/1000000000000) (1137255845/2147483648) (-682554667/2147483648) 1 8 ![52,0,4] ![(47/1600),0,(1/4)] ![(3/3200),1,(1/4)] 196083080657950199076638792089600000000000 125916818440364099846293814807484514172928 592288563743291995488144850944000000000000 raw00190 affine00190
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00190_raw leaf00190_rectangular
    leaf00190_transform leaf00190_sign leaf00190_log
#print axioms leaf00190_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
