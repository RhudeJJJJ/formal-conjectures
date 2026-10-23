/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows000
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows001
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows002
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows003
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows004
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows005
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows006
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows007
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows008
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows009
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows010
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows011
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows012
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows013
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows014
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows015
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows016
import Proofs.RadenkovicGutmanD1LCMInverseBernsteinRows017
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open DegreeOneLCMInverseStages DegreeOneLCMInversePieces
def rows01753 : Fin 89 → NestedInteger.Poly 2 := ![bernsteinRow00,bernsteinRow01,bernsteinRow02,bernsteinRow03,bernsteinRow04,bernsteinRow05,bernsteinRow06,bernsteinRow07,bernsteinRow08,bernsteinRow09,bernsteinRow10,bernsteinRow11,bernsteinRow12,bernsteinRow13,bernsteinRow14,bernsteinRow15,bernsteinRow16,bernsteinRow17,bernsteinRow18,bernsteinRow19,bernsteinRow20,bernsteinRow21,bernsteinRow22,bernsteinRow23,bernsteinRow24,bernsteinRow25,bernsteinRow26,bernsteinRow27,bernsteinRow28,bernsteinRow29,bernsteinRow30,bernsteinRow31,bernsteinRow32,bernsteinRow33,bernsteinRow34,bernsteinRow35,bernsteinRow36,bernsteinRow37,bernsteinRow38,bernsteinRow39,bernsteinRow40,bernsteinRow41,bernsteinRow42,bernsteinRow43,bernsteinRow44,bernsteinRow45,bernsteinRow46,bernsteinRow47,bernsteinRow48,bernsteinRow49,bernsteinRow50,bernsteinRow51,bernsteinRow52,bernsteinRow53,bernsteinRow54,bernsteinRow55,bernsteinRow56,bernsteinRow57,bernsteinRow58,bernsteinRow59,bernsteinRow60,bernsteinRow61,bernsteinRow62,bernsteinRow63,bernsteinRow64,bernsteinRow65,bernsteinRow66,bernsteinRow67,bernsteinRow68,bernsteinRow69,bernsteinRow70,bernsteinRow71,bernsteinRow72,bernsteinRow73,bernsteinRow74,bernsteinRow75,bernsteinRow76,bernsteinRow77,bernsteinRow78,bernsteinRow79,bernsteinRow80,bernsteinRow81,bernsteinRow82,bernsteinRow83,bernsteinRow84,bernsteinRow85,bernsteinRow86,bernsteinRow87,bernsteinRow88]
theorem leaf01753_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] affine01753=true := by
  apply IntegerBernsteinRows.checked ![88,4,4] affine01753 rows01753 (by decide +kernel)
  · intro j
    fin_cases j
    · exact bernsteinRow00_identity
    · exact bernsteinRow01_identity
    · exact bernsteinRow02_identity
    · exact bernsteinRow03_identity
    · exact bernsteinRow04_identity
    · exact bernsteinRow05_identity
    · exact bernsteinRow06_identity
    · exact bernsteinRow07_identity
    · exact bernsteinRow08_identity
    · exact bernsteinRow09_identity
    · exact bernsteinRow10_identity
    · exact bernsteinRow11_identity
    · exact bernsteinRow12_identity
    · exact bernsteinRow13_identity
    · exact bernsteinRow14_identity
    · exact bernsteinRow15_identity
    · exact bernsteinRow16_identity
    · exact bernsteinRow17_identity
    · exact bernsteinRow18_identity
    · exact bernsteinRow19_identity
    · exact bernsteinRow20_identity
    · exact bernsteinRow21_identity
    · exact bernsteinRow22_identity
    · exact bernsteinRow23_identity
    · exact bernsteinRow24_identity
    · exact bernsteinRow25_identity
    · exact bernsteinRow26_identity
    · exact bernsteinRow27_identity
    · exact bernsteinRow28_identity
    · exact bernsteinRow29_identity
    · exact bernsteinRow30_identity
    · exact bernsteinRow31_identity
    · exact bernsteinRow32_identity
    · exact bernsteinRow33_identity
    · exact bernsteinRow34_identity
    · exact bernsteinRow35_identity
    · exact bernsteinRow36_identity
    · exact bernsteinRow37_identity
    · exact bernsteinRow38_identity
    · exact bernsteinRow39_identity
    · exact bernsteinRow40_identity
    · exact bernsteinRow41_identity
    · exact bernsteinRow42_identity
    · exact bernsteinRow43_identity
    · exact bernsteinRow44_identity
    · exact bernsteinRow45_identity
    · exact bernsteinRow46_identity
    · exact bernsteinRow47_identity
    · exact bernsteinRow48_identity
    · exact bernsteinRow49_identity
    · exact bernsteinRow50_identity
    · exact bernsteinRow51_identity
    · exact bernsteinRow52_identity
    · exact bernsteinRow53_identity
    · exact bernsteinRow54_identity
    · exact bernsteinRow55_identity
    · exact bernsteinRow56_identity
    · exact bernsteinRow57_identity
    · exact bernsteinRow58_identity
    · exact bernsteinRow59_identity
    · exact bernsteinRow60_identity
    · exact bernsteinRow61_identity
    · exact bernsteinRow62_identity
    · exact bernsteinRow63_identity
    · exact bernsteinRow64_identity
    · exact bernsteinRow65_identity
    · exact bernsteinRow66_identity
    · exact bernsteinRow67_identity
    · exact bernsteinRow68_identity
    · exact bernsteinRow69_identity
    · exact bernsteinRow70_identity
    · exact bernsteinRow71_identity
    · exact bernsteinRow72_identity
    · exact bernsteinRow73_identity
    · exact bernsteinRow74_identity
    · exact bernsteinRow75_identity
    · exact bernsteinRow76_identity
    · exact bernsteinRow77_identity
    · exact bernsteinRow78_identity
    · exact bernsteinRow79_identity
    · exact bernsteinRow80_identity
    · exact bernsteinRow81_identity
    · exact bernsteinRow82_identity
    · exact bernsteinRow83_identity
    · exact bernsteinRow84_identity
    · exact bernsteinRow85_identity
    · exact bernsteinRow86_identity
    · exact bernsteinRow87_identity
    · exact bernsteinRow88_identity
  · intro j
    fin_cases j
    · exact bernsteinRow00_positive
    · exact bernsteinRow01_positive
    · exact bernsteinRow02_positive
    · exact bernsteinRow03_positive
    · exact bernsteinRow04_positive
    · exact bernsteinRow05_positive
    · exact bernsteinRow06_positive
    · exact bernsteinRow07_positive
    · exact bernsteinRow08_positive
    · exact bernsteinRow09_positive
    · exact bernsteinRow10_positive
    · exact bernsteinRow11_positive
    · exact bernsteinRow12_positive
    · exact bernsteinRow13_positive
    · exact bernsteinRow14_positive
    · exact bernsteinRow15_positive
    · exact bernsteinRow16_positive
    · exact bernsteinRow17_positive
    · exact bernsteinRow18_positive
    · exact bernsteinRow19_positive
    · exact bernsteinRow20_positive
    · exact bernsteinRow21_positive
    · exact bernsteinRow22_positive
    · exact bernsteinRow23_positive
    · exact bernsteinRow24_positive
    · exact bernsteinRow25_positive
    · exact bernsteinRow26_positive
    · exact bernsteinRow27_positive
    · exact bernsteinRow28_positive
    · exact bernsteinRow29_positive
    · exact bernsteinRow30_positive
    · exact bernsteinRow31_positive
    · exact bernsteinRow32_positive
    · exact bernsteinRow33_positive
    · exact bernsteinRow34_positive
    · exact bernsteinRow35_positive
    · exact bernsteinRow36_positive
    · exact bernsteinRow37_positive
    · exact bernsteinRow38_positive
    · exact bernsteinRow39_positive
    · exact bernsteinRow40_positive
    · exact bernsteinRow41_positive
    · exact bernsteinRow42_positive
    · exact bernsteinRow43_positive
    · exact bernsteinRow44_positive
    · exact bernsteinRow45_positive
    · exact bernsteinRow46_positive
    · exact bernsteinRow47_positive
    · exact bernsteinRow48_positive
    · exact bernsteinRow49_positive
    · exact bernsteinRow50_positive
    · exact bernsteinRow51_positive
    · exact bernsteinRow52_positive
    · exact bernsteinRow53_positive
    · exact bernsteinRow54_positive
    · exact bernsteinRow55_positive
    · exact bernsteinRow56_positive
    · exact bernsteinRow57_positive
    · exact bernsteinRow58_positive
    · exact bernsteinRow59_positive
    · exact bernsteinRow60_positive
    · exact bernsteinRow61_positive
    · exact bernsteinRow62_positive
    · exact bernsteinRow63_positive
    · exact bernsteinRow64_positive
    · exact bernsteinRow65_positive
    · exact bernsteinRow66_positive
    · exact bernsteinRow67_positive
    · exact bernsteinRow68_positive
    · exact bernsteinRow69_positive
    · exact bernsteinRow70_positive
    · exact bernsteinRow71_positive
    · exact bernsteinRow72_positive
    · exact bernsteinRow73_positive
    · exact bernsteinRow74_positive
    · exact bernsteinRow75_positive
    · exact bernsteinRow76_positive
    · exact bernsteinRow77_positive
    · exact bernsteinRow78_positive
    · exact bernsteinRow79_positive
    · exact bernsteinRow80_positive
    · exact bernsteinRow81_positive
    · exact bernsteinRow82_positive
    · exact bernsteinRow83_positive
    · exact bernsteinRow84_positive
    · exact bernsteinRow85_positive
    · exact bernsteinRow86_positive
    · exact bernsteinRow87_positive
    · exact bernsteinRow88_positive
#print axioms leaf01753_sign
theorem leaf01753_log : RationalLog.accepts (536871935/536870912) (4091/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01753_log
def leaf01753 : FastNestedCellData.Cell := IntegerScaledCell.make DegreeOneNormPack00.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1] 168684840550400000000000 ![1024,1,1] affine01753
theorem leaf01753_checked : FastNestedCellData.accepts 1 4 4 leaf01753=true :=
  IntegerPiecewiseCell.accepts_make DegreeOneIntegerNorm00.pack true (1571/1000000000000) (536871935/536870912) (4091/4294967296) 0 8 ![88,4,4] ![(1/1024),0,0] ![(1/1024),1,1] 168684840550400000000000 168685162242004389465867 107374387168685161977000000000000 ![1,0,0] ![1,1,1] ![1024,1,1] raw01753 inner01753 affine01753
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    leaf01753_raw leaf01753_rectangular leaf01753_inner affine01753_eval leaf01753_sign leaf01753_log
#print axioms leaf01753_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInverseRows
