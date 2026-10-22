/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00446 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 303474355014169677417938944000000000000 331151841181646601050694769174565093376 54698709574386790018421096448000000000000))
theorem leaf00446_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 303474355014169677417938944000000000000 331151841181646601050694769174565093376 54698709574386790018421096448000000000000 raw00446=true := by decide +kernel
#print axioms leaf00446_raw
theorem leaf00446_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00446=true := by decide +kernel
#print axioms leaf00446_rectangular
def affine00446 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00446 (IntegerComputedClassCell.leftNumerator ![(15/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(15/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(15/64),0,(3/4)] ![(1/64),1,(1/4)]))
theorem leaf00446_transform : affine00446=(NestedInteger.clearedAll 3 raw00446 (IntegerComputedClassCell.leftNumerator ![(15/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(15/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(15/64),0,(3/4)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00446_transform
theorem leaf00446_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00446=true := by decide +kernel
#print axioms leaf00446_sign
theorem leaf00446_log : RationalLog.accepts (4658474257/4294967296) (174470249/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00446_log
def leaf00446 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (1513526753/250000000000) (4658474257/4294967296) (174470249/4294967296) 0 8 ![52,0,4] ![(15/64),0,(3/4)] ![(1/64),1,(1/4)] affine00446
theorem leaf00446_checked : FastNestedCellData.accepts 1 0 4 leaf00446=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (1513526753/250000000000) (4658474257/4294967296) (174470249/4294967296) 0 8 ![52,0,4] ![(15/64),0,(3/4)] ![(1/64),1,(1/4)] 303474355014169677417938944000000000000 331151841181646601050694769174565093376 54698709574386790018421096448000000000000 raw00446 affine00446
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00446_raw leaf00446_rectangular
    leaf00446_transform leaf00446_sign leaf00446_log
#print axioms leaf00446_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
