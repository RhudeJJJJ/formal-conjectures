/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFastArmCoverIntegral
import Proofs.RadenkovicGutmanD1Long10Chunk000
import Proofs.RadenkovicGutmanD1Long10Chunk001
import Proofs.RadenkovicGutmanD1Long10Chunk002
import Proofs.RadenkovicGutmanD1Long10Chunk003
import Proofs.RadenkovicGutmanD1Long10Chunk004
import Proofs.RadenkovicGutmanD1Long10Chunk005
import Proofs.RadenkovicGutmanD1Long10Chunk006
import Proofs.RadenkovicGutmanD1Long10Chunk007
import Proofs.RadenkovicGutmanD1Long10Chunk008
import Proofs.RadenkovicGutmanD1Long10Chunk009
import Proofs.RadenkovicGutmanD1Long10Chunk010
import Proofs.RadenkovicGutmanD1Long10Chunk011
import Proofs.RadenkovicGutmanD1Long10Chunk012
import Proofs.RadenkovicGutmanD1Long10Chunk013
import Proofs.RadenkovicGutmanD1Long10Chunk014
import Proofs.RadenkovicGutmanD1Long10Chunk015
import Proofs.RadenkovicGutmanD1Long10Chunk016
import Proofs.RadenkovicGutmanD1Long10Chunk017
import Proofs.RadenkovicGutmanD1Long10Chunk018
import Proofs.RadenkovicGutmanD1Long10Chunk019
import Proofs.RadenkovicGutmanD1Long10Chunk020
import Proofs.RadenkovicGutmanD1Long10Chunk021
import Proofs.RadenkovicGutmanD1Long10Chunk022
import Proofs.RadenkovicGutmanD1Long10Chunk023
import Proofs.RadenkovicGutmanD1Long10Chunk024
import Proofs.RadenkovicGutmanD1Long10Chunk025
import Proofs.RadenkovicGutmanD1Long10Chunk026
import Proofs.RadenkovicGutmanD1Long10Chunk027
import Proofs.RadenkovicGutmanD1Long10Chunk028
import Proofs.RadenkovicGutmanD1Long10Chunk029
import Proofs.RadenkovicGutmanD1Long10Chunk030
import Proofs.RadenkovicGutmanD1Long10Chunk031
import Proofs.RadenkovicGutmanD1Long10Chunk032
import Proofs.RadenkovicGutmanD1Long10Chunk033
import Proofs.RadenkovicGutmanD1Long10Chunk034
import Proofs.RadenkovicGutmanD1Long10Chunk035
import Proofs.RadenkovicGutmanD1Long10Chunk036
import Proofs.RadenkovicGutmanD1Long10Chunk037
import Proofs.RadenkovicGutmanD1Long10Chunk038
import Proofs.RadenkovicGutmanD1Long10Chunk039
import Proofs.RadenkovicGutmanD1Long10Chunk040
import Proofs.RadenkovicGutmanD1Long10Chunk041
import Proofs.RadenkovicGutmanD1Long10Chunk042
import Proofs.RadenkovicGutmanD1Long10Chunk043
import Proofs.RadenkovicGutmanD1Long10Chunk044
import Proofs.RadenkovicGutmanD1Long10Chunk045
import Proofs.RadenkovicGutmanD1Long10Chunk046
import Proofs.RadenkovicGutmanD1Long10Chunk047
import Proofs.RadenkovicGutmanD1Long10Chunk048
import Proofs.RadenkovicGutmanD1Long10Chunk049
import Proofs.RadenkovicGutmanD1Long10Chunk050
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
open FastArmCoverIntegral
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def cover000 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00000) (.leaf leaf00001)) (.leaf leaf00002))
theorem cover000_checked : FastArmCover.accepts 1 0 4 (1/1000) (1/800) 0 1 0 1 (-31500787239101063476977/4722366482869645213696) cover000=true := by
  unfold cover000
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00000_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00001_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00002_checked
    · decide +kernel
    · decide +kernel
def slice000 : Slice := ⟨cover000,(1/1000),(1/800),(-31500787239101063476977/4722366482869645213696)⟩
theorem slice000_checked : accepts 1 0 4 slice000=true :=
  accepts_of_checks 1 0 4 slice000 (by decide +kernel) (by decide +kernel) cover000_checked
def cover001 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00003) (.leaf leaf00004)) (.leaf leaf00005))
theorem cover001_checked : FastArmCover.accepts 1 0 4 (1/800) (3/2000) 0 1 0 1 (-27285613535/4294967296) cover001=true := by
  unfold cover001
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00003_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00004_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00005_checked
    · decide +kernel
    · decide +kernel
def slice001 : Slice := ⟨cover001,(1/800),(3/2000),(-27285613535/4294967296)⟩
theorem slice001_checked : accepts 1 0 4 slice001=true :=
  accepts_of_checks 1 0 4 slice001 (by decide +kernel) (by decide +kernel) cover001_checked
def cover002 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00006) (.leaf leaf00007)) (.leaf leaf00008))
theorem cover002_checked : FastArmCover.accepts 1 0 4 (3/2000) (7/4000) 0 1 0 1 (-817774085/134217728) cover002=true := by
  unfold cover002
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00006_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00007_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00008_checked
    · decide +kernel
    · decide +kernel
def slice002 : Slice := ⟨cover002,(3/2000),(7/4000),(-817774085/134217728)⟩
theorem slice002_checked : accepts 1 0 4 slice002=true :=
  accepts_of_checks 1 0 4 slice002 (by decide +kernel) (by decide +kernel) cover002_checked
def cover003 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00009) (.leaf leaf00010)) (.leaf leaf00011))
theorem cover003_checked : FastArmCover.accepts 1 0 4 (7/4000) (1/500) 0 1 0 1 (-25224356225/4294967296) cover003=true := by
  unfold cover003
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00009_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00010_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00011_checked
    · decide +kernel
    · decide +kernel
def slice003 : Slice := ⟨cover003,(7/4000),(1/500),(-25224356225/4294967296)⟩
theorem slice003_checked : accepts 1 0 4 slice003=true :=
  accepts_of_checks 1 0 4 slice003 (by decide +kernel) (by decide +kernel) cover003_checked
def cover004 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00012) (.leaf leaf00013)) (.leaf leaf00014))
theorem cover004_checked : FastArmCover.accepts 1 0 4 (1/500) (7/3200) 0 1 0 1 (-24435634917/4294967296) cover004=true := by
  unfold cover004
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00012_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00013_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00014_checked
    · decide +kernel
    · decide +kernel
def slice004 : Slice := ⟨cover004,(1/500),(7/3200),(-24435634917/4294967296)⟩
theorem slice004_checked : accepts 1 0 4 slice004=true :=
  accepts_of_checks 1 0 4 slice004 (by decide +kernel) (by decide +kernel) cover004_checked
def cover005 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00015) (.leaf leaf00016)) (.leaf leaf00017))
theorem cover005_checked : FastArmCover.accepts 1 0 4 (7/3200) (19/8000) 0 1 0 1 (-23885212793/4294967296) cover005=true := by
  unfold cover005
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00015_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00016_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00017_checked
    · decide +kernel
    · decide +kernel
def slice005 : Slice := ⟨cover005,(7/3200),(19/8000),(-23885212793/4294967296)⟩
theorem slice005_checked : accepts 1 0 4 slice005=true :=
  accepts_of_checks 1 0 4 slice005 (by decide +kernel) (by decide +kernel) cover005_checked
def cover006 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00018) (.leaf leaf00019)) (.leaf leaf00020))
theorem cover006_checked : FastArmCover.accepts 1 0 4 (19/8000) (41/16000) 0 1 0 1 (-23380988281/4294967296) cover006=true := by
  unfold cover006
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00018_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00019_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00020_checked
    · decide +kernel
    · decide +kernel
def slice006 : Slice := ⟨cover006,(19/8000),(41/16000),(-23380988281/4294967296)⟩
theorem slice006_checked : accepts 1 0 4 slice006=true :=
  accepts_of_checks 1 0 4 slice006 (by decide +kernel) (by decide +kernel) cover006_checked
def cover007 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00021) (.leaf leaf00022)) (.leaf leaf00023))
theorem cover007_checked : FastArmCover.accepts 1 0 4 (41/16000) (11/4000) 0 1 0 1 (-5729008611/1073741824) cover007=true := by
  unfold cover007
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00021_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00022_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00023_checked
    · decide +kernel
    · decide +kernel
def slice007 : Slice := ⟨cover007,(41/16000),(11/4000),(-5729008611/1073741824)⟩
theorem slice007_checked : accepts 1 0 4 slice007=true :=
  accepts_of_checks 1 0 4 slice007 (by decide +kernel) (by decide +kernel) cover007_checked
def cover008 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00024) (.leaf leaf00025)) (.leaf leaf00026))
theorem cover008_checked : FastArmCover.accepts 1 0 4 (11/4000) (47/16000) 0 1 0 1 (-5621201393/1073741824) cover008=true := by
  unfold cover008
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00024_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00025_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00026_checked
    · decide +kernel
    · decide +kernel
def slice008 : Slice := ⟨cover008,(11/4000),(47/16000),(-5621201393/1073741824)⟩
theorem slice008_checked : accepts 1 0 4 slice008=true :=
  accepts_of_checks 1 0 4 slice008 (by decide +kernel) (by decide +kernel) cover008_checked
def cover009 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00027) (.leaf leaf00028)) (.leaf leaf00029))
theorem cover009_checked : FastArmCover.accepts 1 0 4 (47/16000) (1/320) 0 1 0 1 (-172522827/33554432) cover009=true := by
  unfold cover009
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00027_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00028_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00029_checked
    · decide +kernel
    · decide +kernel
def slice009 : Slice := ⟨cover009,(47/16000),(1/320),(-172522827/33554432)⟩
theorem slice009_checked : accepts 1 0 4 slice009=true :=
  accepts_of_checks 1 0 4 slice009 (by decide +kernel) (by decide +kernel) cover009_checked
def cover010 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00030) (.leaf leaf00031)) (.leaf leaf00032))
theorem cover010_checked : FastArmCover.accepts 1 0 4 (1/320) (7/2000) 0 1 0 1 (-5413584905/1073741824) cover010=true := by
  unfold cover010
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00030_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00031_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00032_checked
    · decide +kernel
    · decide +kernel
def slice010 : Slice := ⟨cover010,(1/320),(7/2000),(-5413584905/1073741824)⟩
theorem slice010_checked : accepts 1 0 4 slice010=true :=
  accepts_of_checks 1 0 4 slice010 (by decide +kernel) (by decide +kernel) cover010_checked
def cover011 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00033) (.leaf leaf00034)) (.leaf leaf00035))
theorem cover011_checked : FastArmCover.accepts 1 0 4 (7/2000) (31/8000) 0 1 0 1 (-20974135691/4294967296) cover011=true := by
  unfold cover011
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00033_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00034_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00035_checked
    · decide +kernel
    · decide +kernel
def slice011 : Slice := ⟨cover011,(7/2000),(31/8000),(-20974135691/4294967296)⟩
theorem slice011_checked : accepts 1 0 4 slice011=true :=
  accepts_of_checks 1 0 4 slice011 (by decide +kernel) (by decide +kernel) cover011_checked
def cover012 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00036) (.leaf leaf00037)) (.leaf leaf00038))
theorem cover012_checked : FastArmCover.accepts 1 0 4 (31/8000) (17/4000) 0 1 0 1 (-20365692467/4294967296) cover012=true := by
  unfold cover012
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00036_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00037_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00038_checked
    · decide +kernel
    · decide +kernel
def slice012 : Slice := ⟨cover012,(31/8000),(17/4000),(-20365692467/4294967296)⟩
theorem slice012_checked : accepts 1 0 4 slice012=true :=
  accepts_of_checks 1 0 4 slice012 (by decide +kernel) (by decide +kernel) cover012_checked
def cover013 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00039) (.leaf leaf00040)) (.leaf leaf00041))
theorem cover013_checked : FastArmCover.accepts 1 0 4 (17/4000) (37/8000) 0 1 0 1 (-19815893641/4294967296) cover013=true := by
  unfold cover013
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00039_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00040_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00041_checked
    · decide +kernel
    · decide +kernel
def slice013 : Slice := ⟨cover013,(17/4000),(37/8000),(-19815893641/4294967296)⟩
theorem slice013_checked : accepts 1 0 4 slice013=true :=
  accepts_of_checks 1 0 4 slice013 (by decide +kernel) (by decide +kernel) cover013_checked
def cover014 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00042) (.leaf leaf00043)) (.leaf leaf00044))
theorem cover014_checked : FastArmCover.accepts 1 0 4 (37/8000) (1/200) 0 1 0 1 (-9657451447/2147483648) cover014=true := by
  unfold cover014
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00042_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00043_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00044_checked
    · decide +kernel
    · decide +kernel
def slice014 : Slice := ⟨cover014,(37/8000),(1/200),(-9657451447/2147483648)⟩
theorem slice014_checked : accepts 1 0 4 slice014=true :=
  accepts_of_checks 1 0 4 slice014 (by decide +kernel) (by decide +kernel) cover014_checked
def cover015 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00045) (.leaf leaf00046)) (.leaf leaf00047))
theorem cover015_checked : FastArmCover.accepts 1 0 4 (1/200) (17/3200) 0 1 0 1 (-4716280979/1073741824) cover015=true := by
  unfold cover015
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00045_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00046_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00047_checked
    · decide +kernel
    · decide +kernel
def slice015 : Slice := ⟨cover015,(1/200),(17/3200),(-4716280979/1073741824)⟩
theorem slice015_checked : accepts 1 0 4 slice015=true :=
  accepts_of_checks 1 0 4 slice015 (by decide +kernel) (by decide +kernel) cover015_checked
def cover016 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00048) (.leaf leaf00049)) (.leaf leaf00050))
theorem cover016_checked : FastArmCover.accepts 1 0 4 (17/3200) (9/1600) 0 1 0 1 (-18508468355/4294967296) cover016=true := by
  unfold cover016
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00048_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00049_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00050_checked
    · decide +kernel
    · decide +kernel
def slice016 : Slice := ⟨cover016,(17/3200),(9/1600),(-18508468355/4294967296)⟩
theorem slice016_checked : accepts 1 0 4 slice016=true :=
  accepts_of_checks 1 0 4 slice016 (by decide +kernel) (by decide +kernel) cover016_checked
def cover017 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00051) (.leaf leaf00052)) (.leaf leaf00053))
theorem cover017_checked : FastArmCover.accepts 1 0 4 (9/1600) (19/3200) 0 1 0 1 (-9086803263/2147483648) cover017=true := by
  unfold cover017
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00051_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00052_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00053_checked
    · decide +kernel
    · decide +kernel
def slice017 : Slice := ⟨cover017,(9/1600),(19/3200),(-9086803263/2147483648)⟩
theorem slice017_checked : accepts 1 0 4 slice017=true :=
  accepts_of_checks 1 0 4 slice017 (by decide +kernel) (by decide +kernel) cover017_checked
def cover018 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00054) (.leaf leaf00055)) (.leaf leaf00056))
theorem cover018_checked : FastArmCover.accepts 1 0 4 (19/3200) (1/160) 0 1 0 1 (-4464546855/1073741824) cover018=true := by
  unfold cover018
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00054_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00055_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00056_checked
    · decide +kernel
    · decide +kernel
def slice018 : Slice := ⟨cover018,(19/3200),(1/160),(-4464546855/1073741824)⟩
theorem slice018_checked : accepts 1 0 4 slice018=true :=
  accepts_of_checks 1 0 4 slice018 (by decide +kernel) (by decide +kernel) cover018_checked
def cover019 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00057) (.leaf leaf00058)) (.leaf leaf00059))
theorem cover019_checked : FastArmCover.accepts 1 0 4 (1/160) (21/3200) 0 1 0 1 (-8780108949/2147483648) cover019=true := by
  unfold cover019
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00057_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00058_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00059_checked
    · decide +kernel
    · decide +kernel
def slice019 : Slice := ⟨cover019,(1/160),(21/3200),(-8780108949/2147483648)⟩
theorem slice019_checked : accepts 1 0 4 slice019=true :=
  accepts_of_checks 1 0 4 slice019 (by decide +kernel) (by decide +kernel) cover019_checked
def cover020 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00060) (.leaf leaf00061)) (.leaf leaf00062))
theorem cover020_checked : FastArmCover.accepts 1 0 4 (21/3200) (11/1600) 0 1 0 1 (-8638994897/2147483648) cover020=true := by
  unfold cover020
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00060_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00061_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00062_checked
    · decide +kernel
    · decide +kernel
def slice020 : Slice := ⟨cover020,(21/3200),(11/1600),(-8638994897/2147483648)⟩
theorem slice020_checked : accepts 1 0 4 slice020=true :=
  accepts_of_checks 1 0 4 slice020 (by decide +kernel) (by decide +kernel) cover020_checked
def cover021 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00063) (.leaf leaf00064)) (.leaf leaf00065))
theorem cover021_checked : FastArmCover.accepts 1 0 4 (11/1600) (23/3200) 0 1 0 1 (-17010038105/4294967296) cover021=true := by
  unfold cover021
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00063_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00064_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00065_checked
    · decide +kernel
    · decide +kernel
def slice021 : Slice := ⟨cover021,(11/1600),(23/3200),(-17010038105/4294967296)⟩
theorem slice021_checked : accepts 1 0 4 slice021=true :=
  accepts_of_checks 1 0 4 slice021 (by decide +kernel) (by decide +kernel) cover021_checked
def cover022 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00066) (.leaf leaf00067)) (.leaf leaf00068))
theorem cover022_checked : FastArmCover.accepts 1 0 4 (23/3200) (3/400) 0 1 0 1 (-1047192975/268435456) cover022=true := by
  unfold cover022
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00066_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00067_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00068_checked
    · decide +kernel
    · decide +kernel
def slice022 : Slice := ⟨cover022,(23/3200),(3/400),(-1047192975/268435456)⟩
theorem slice022_checked : accepts 1 0 4 slice022=true :=
  accepts_of_checks 1 0 4 slice022 (by decide +kernel) (by decide +kernel) cover022_checked
def cover023 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00069) (.leaf leaf00070)) (.leaf leaf00071))
theorem cover023_checked : FastArmCover.accepts 1 0 4 (3/400) (1/128) 0 1 0 1 (-4128006745/1073741824) cover023=true := by
  unfold cover023
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00069_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00070_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00071_checked
    · decide +kernel
    · decide +kernel
def slice023 : Slice := ⟨cover023,(3/400),(1/128),(-4128006745/1073741824)⟩
theorem slice023_checked : accepts 1 0 4 slice023=true :=
  accepts_of_checks 1 0 4 slice023 (by decide +kernel) (by decide +kernel) cover023_checked
def cover024 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00072) (.leaf leaf00073)) (.leaf leaf00074))
theorem cover024_checked : FastArmCover.accepts 1 0 4 (1/128) (13/1600) 0 1 0 1 (-16279877881/4294967296) cover024=true := by
  unfold cover024
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00072_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00073_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00074_checked
    · decide +kernel
    · decide +kernel
def slice024 : Slice := ⟨cover024,(1/128),(13/1600),(-16279877881/4294967296)⟩
theorem slice024_checked : accepts 1 0 4 slice024=true :=
  accepts_of_checks 1 0 4 slice024 (by decide +kernel) (by decide +kernel) cover024_checked
def cover025 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00075) (.leaf leaf00076)) (.leaf leaf00077))
theorem cover025_checked : FastArmCover.accepts 1 0 4 (13/1600) (27/3200) 0 1 0 1 (-8028888505/2147483648) cover025=true := by
  unfold cover025
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00075_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00076_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00077_checked
    · decide +kernel
    · decide +kernel
def slice025 : Slice := ⟨cover025,(13/1600),(27/3200),(-8028888505/2147483648)⟩
theorem slice025_checked : accepts 1 0 4 slice025=true :=
  accepts_of_checks 1 0 4 slice025 (by decide +kernel) (by decide +kernel) cover025_checked
def cover026 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00078) (.leaf leaf00079)) (.leaf leaf00080))
theorem cover026_checked : FastArmCover.accepts 1 0 4 (27/3200) (7/800) 0 1 0 1 (-7922479735/2147483648) cover026=true := by
  unfold cover026
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00078_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00079_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00080_checked
    · decide +kernel
    · decide +kernel
def slice026 : Slice := ⟨cover026,(27/3200),(7/800),(-7922479735/2147483648)⟩
theorem slice026_checked : accepts 1 0 4 slice026=true :=
  accepts_of_checks 1 0 4 slice026 (by decide +kernel) (by decide +kernel) cover026_checked
def cover027 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00081) (.leaf leaf00082)) (.leaf leaf00083))
theorem cover027_checked : FastArmCover.accepts 1 0 4 (7/800) (29/3200) 0 1 0 1 (-3910185543/1073741824) cover027=true := by
  unfold cover027
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00081_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00082_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00083_checked
    · decide +kernel
    · decide +kernel
def slice027 : Slice := ⟨cover027,(7/800),(29/3200),(-3910185543/1073741824)⟩
theorem slice027_checked : accepts 1 0 4 slice027=true :=
  accepts_of_checks 1 0 4 slice027 (by decide +kernel) (by decide +kernel) cover027_checked
def cover028 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00084) (.leaf leaf00085)) (.leaf leaf00086))
theorem cover028_checked : FastArmCover.accepts 1 0 4 (29/3200) (3/320) 0 1 0 1 (-7722257057/2147483648) cover028=true := by
  unfold cover028
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00084_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00085_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00086_checked
    · decide +kernel
    · decide +kernel
def slice028 : Slice := ⟨cover028,(29/3200),(3/320),(-7722257057/2147483648)⟩
theorem slice028_checked : accepts 1 0 4 slice028=true :=
  accepts_of_checks 1 0 4 slice028 (by decide +kernel) (by decide +kernel) cover028_checked
def cover029 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00087) (.leaf leaf00088)) (.leaf leaf00089))
theorem cover029_checked : FastArmCover.accepts 1 0 4 (3/320) (31/3200) 0 1 0 1 (-15255724089/4294967296) cover029=true := by
  unfold cover029
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00087_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00088_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00089_checked
    · decide +kernel
    · decide +kernel
def slice029 : Slice := ⟨cover029,(3/320),(31/3200),(-15255724089/4294967296)⟩
theorem slice029_checked : accepts 1 0 4 slice029=true :=
  accepts_of_checks 1 0 4 slice029 (by decide +kernel) (by decide +kernel) cover029_checked
def cover030 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00090) (.leaf leaf00091)) (.leaf leaf00092))
theorem cover030_checked : FastArmCover.accepts 1 0 4 (31/3200) (1/100) 0 1 0 1 (-3768469335/1073741824) cover030=true := by
  unfold cover030
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00090_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00091_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00092_checked
    · decide +kernel
    · decide +kernel
def slice030 : Slice := ⟨cover030,(31/3200),(1/100),(-3768469335/1073741824)⟩
theorem slice030_checked : accepts 1 0 4 slice030=true :=
  accepts_of_checks 1 0 4 slice030 (by decide +kernel) (by decide +kernel) cover030_checked
def cover031 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00093) (.leaf leaf00094)) (.leaf leaf00095))
theorem cover031_checked : FastArmCover.accepts 1 0 4 (1/100) (33/3200) 0 1 0 1 (-14898524661/4294967296) cover031=true := by
  unfold cover031
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00093_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00094_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00095_checked
    · decide +kernel
    · decide +kernel
def slice031 : Slice := ⟨cover031,(1/100),(33/3200),(-14898524661/4294967296)⟩
theorem slice031_checked : accepts 1 0 4 slice031=true :=
  accepts_of_checks 1 0 4 slice031 (by decide +kernel) (by decide +kernel) cover031_checked
def cover032 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00096) (.leaf leaf00097)) (.leaf leaf00098))
theorem cover032_checked : FastArmCover.accepts 1 0 4 (33/3200) (17/1600) 0 1 0 1 (-7364629007/2147483648) cover032=true := by
  unfold cover032
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00096_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00097_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00098_checked
    · decide +kernel
    · decide +kernel
def slice032 : Slice := ⟨cover032,(33/3200),(17/1600),(-7364629007/2147483648)⟩
theorem slice032_checked : accepts 1 0 4 slice032=true :=
  accepts_of_checks 1 0 4 slice032 (by decide +kernel) (by decide +kernel) cover032_checked
def cover033 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00099) (.leaf leaf00100)) (.leaf leaf00101))
theorem cover033_checked : FastArmCover.accepts 1 0 4 (17/1600) (7/640) 0 1 0 1 (-14565706625/4294967296) cover033=true := by
  unfold cover033
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00099_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00100_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00101_checked
    · decide +kernel
    · decide +kernel
def slice033 : Slice := ⟨cover033,(17/1600),(7/640),(-14565706625/4294967296)⟩
theorem slice033_checked : accepts 1 0 4 slice033=true :=
  accepts_of_checks 1 0 4 slice033 (by decide +kernel) (by decide +kernel) cover033_checked
def cover034 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00102) (.leaf leaf00103)) (.leaf leaf00104))
theorem cover034_checked : FastArmCover.accepts 1 0 4 (7/640) (9/800) 0 1 0 1 (-3601882643/1073741824) cover034=true := by
  unfold cover034
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00102_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00103_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00104_checked
    · decide +kernel
    · decide +kernel
def slice034 : Slice := ⟨cover034,(7/640),(9/800),(-3601882643/1073741824)⟩
theorem slice034_checked : accepts 1 0 4 slice034=true :=
  accepts_of_checks 1 0 4 slice034 (by decide +kernel) (by decide +kernel) cover034_checked
def cover035 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00105) (.leaf leaf00106)) (.leaf leaf00107))
theorem cover035_checked : FastArmCover.accepts 1 0 4 (9/800) (37/3200) 0 1 0 1 (-3563604791/1073741824) cover035=true := by
  unfold cover035
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00105_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00106_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00107_checked
    · decide +kernel
    · decide +kernel
def slice035 : Slice := ⟨cover035,(9/800),(37/3200),(-3563604791/1073741824)⟩
theorem slice035_checked : accepts 1 0 4 slice035=true :=
  accepts_of_checks 1 0 4 slice035 (by decide +kernel) (by decide +kernel) cover035_checked
def cover036 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00108) (.leaf leaf00109)) (.leaf leaf00110))
theorem cover036_checked : FastArmCover.accepts 1 0 4 (37/3200) (19/1600) 0 1 0 1 (-14106087497/4294967296) cover036=true := by
  unfold cover036
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00108_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00109_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00110_checked
    · decide +kernel
    · decide +kernel
def slice036 : Slice := ⟨cover036,(37/3200),(19/1600),(-14106087497/4294967296)⟩
theorem slice036_checked : accepts 1 0 4 slice036=true :=
  accepts_of_checks 1 0 4 slice036 (by decide +kernel) (by decide +kernel) cover036_checked
def cover037 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00111) (.leaf leaf00112)) (.leaf leaf00113))
theorem cover037_checked : FastArmCover.accepts 1 0 4 (19/1600) (1/80) 0 1 0 1 (-6974038723/2147483648) cover037=true := by
  unfold cover037
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00111_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00112_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00113_checked
    · decide +kernel
    · decide +kernel
def slice037 : Slice := ⟨cover037,(19/1600),(1/80),(-6974038723/2147483648)⟩
theorem slice037_checked : accepts 1 0 4 slice037=true :=
  accepts_of_checks 1 0 4 slice037 (by decide +kernel) (by decide +kernel) cover037_checked
def cover038 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00114) (.leaf leaf00115)) (.leaf leaf00116))
theorem cover038_checked : FastArmCover.accepts 1 0 4 (1/80) (21/1600) 0 1 0 1 (-6837126843/2147483648) cover038=true := by
  unfold cover038
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00114_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00115_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00116_checked
    · decide +kernel
    · decide +kernel
def slice038 : Slice := ⟨cover038,(1/80),(21/1600),(-6837126843/2147483648)⟩
theorem slice038_checked : accepts 1 0 4 slice038=true :=
  accepts_of_checks 1 0 4 slice038 (by decide +kernel) (by decide +kernel) cover038_checked
def cover039 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00117) (.leaf leaf00118)) (.leaf leaf00119))
theorem cover039_checked : FastArmCover.accepts 1 0 4 (21/1600) (11/800) 0 1 0 1 (-3353922899/1073741824) cover039=true := by
  unfold cover039
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00117_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00118_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00119_checked
    · decide +kernel
    · decide +kernel
def slice039 : Slice := ⟨cover039,(21/1600),(11/800),(-3353922899/1073741824)⟩
theorem slice039_checked : accepts 1 0 4 slice039=true :=
  accepts_of_checks 1 0 4 slice039 (by decide +kernel) (by decide +kernel) cover039_checked
def cover040 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00120) (.leaf leaf00121)) (.leaf leaf00122))
theorem cover040_checked : FastArmCover.accepts 1 0 4 (11/800) (23/1600) 0 1 0 1 (-13170921253/4294967296) cover040=true := by
  unfold cover040
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00120_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00121_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00122_checked
    · decide +kernel
    · decide +kernel
def slice040 : Slice := ⟨cover040,(11/800),(23/1600),(-13170921253/4294967296)⟩
theorem slice040_checked : accepts 1 0 4 slice040=true :=
  accepts_of_checks 1 0 4 slice040 (by decide +kernel) (by decide +kernel) cover040_checked
def cover041 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00123) (.leaf leaf00124)) (.leaf leaf00125))
theorem cover041_checked : FastArmCover.accepts 1 0 4 (23/1600) (3/200) 0 1 0 1 (-12938668907/4294967296) cover041=true := by
  unfold cover041
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00123_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00124_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00125_checked
    · decide +kernel
    · decide +kernel
def slice041 : Slice := ⟨cover041,(23/1600),(3/200),(-12938668907/4294967296)⟩
theorem slice041_checked : accepts 1 0 4 slice041=true :=
  accepts_of_checks 1 0 4 slice041 (by decide +kernel) (by decide +kernel) cover041_checked
def cover042 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00126) (.leaf leaf00127)) (.leaf leaf00128))
theorem cover042_checked : FastArmCover.accepts 1 0 4 (3/200) (1/64) 0 1 0 1 (-12717822859/4294967296) cover042=true := by
  unfold cover042
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00126_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00127_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00128_checked
    · decide +kernel
    · decide +kernel
def slice042 : Slice := ⟨cover042,(3/200),(1/64),(-12717822859/4294967296)⟩
theorem slice042_checked : accepts 1 0 4 slice042=true :=
  accepts_of_checks 1 0 4 slice042 (by decide +kernel) (by decide +kernel) cover042_checked
def cover043 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00129) (.leaf leaf00130)) (.leaf leaf00131))
theorem cover043_checked : FastArmCover.accepts 1 0 4 (1/64) (13/800) 0 1 0 1 (-3126851897/1073741824) cover043=true := by
  unfold cover043
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00129_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00130_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00131_checked
    · decide +kernel
    · decide +kernel
def slice043 : Slice := ⟨cover043,(1/64),(13/800),(-3126851897/1073741824)⟩
theorem slice043_checked : accepts 1 0 4 slice043=true :=
  accepts_of_checks 1 0 4 slice043 (by decide +kernel) (by decide +kernel) cover043_checked
def cover044 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00132) (.leaf leaf00133)) (.leaf leaf00134))
theorem cover044_checked : FastArmCover.accepts 1 0 4 (13/800) (27/1600) 0 1 0 1 (-1538320289/536870912) cover044=true := by
  unfold cover044
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00132_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00133_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00134_checked
    · decide +kernel
    · decide +kernel
def slice044 : Slice := ⟨cover044,(13/800),(27/1600),(-1538320289/536870912)⟩
theorem slice044_checked : accepts 1 0 4 slice044=true :=
  accepts_of_checks 1 0 4 slice044 (by decide +kernel) (by decide +kernel) cover044_checked
def cover045 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00135) (.leaf leaf00136)) (.leaf leaf00137))
theorem cover045_checked : FastArmCover.accepts 1 0 4 (27/1600) (7/400) 0 1 0 1 (-12114524745/4294967296) cover045=true := by
  unfold cover045
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00135_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00136_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00137_checked
    · decide +kernel
    · decide +kernel
def slice045 : Slice := ⟨cover045,(27/1600),(7/400),(-12114524745/4294967296)⟩
theorem slice045_checked : accepts 1 0 4 slice045=true :=
  accepts_of_checks 1 0 4 slice045 (by decide +kernel) (by decide +kernel) cover045_checked
def cover046 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00138) (.leaf leaf00139)) (.leaf leaf00140))
theorem cover046_checked : FastArmCover.accepts 1 0 4 (7/400) (29/1600) 0 1 0 1 (-5965307763/2147483648) cover046=true := by
  unfold cover046
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00138_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00139_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00140_checked
    · decide +kernel
    · decide +kernel
def slice046 : Slice := ⟨cover046,(7/400),(29/1600),(-5965307763/2147483648)⟩
theorem slice046_checked : accepts 1 0 4 slice046=true :=
  accepts_of_checks 1 0 4 slice046 (by decide +kernel) (by decide +kernel) cover046_checked
def cover047 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00141) (.leaf leaf00142)) (.leaf leaf00143))
theorem cover047_checked : FastArmCover.accepts 1 0 4 (29/1600) (3/160) 0 1 0 1 (-11754228103/4294967296) cover047=true := by
  unfold cover047
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00141_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00142_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00143_checked
    · decide +kernel
    · decide +kernel
def slice047 : Slice := ⟨cover047,(29/1600),(3/160),(-11754228103/4294967296)⟩
theorem slice047_checked : accepts 1 0 4 slice047=true :=
  accepts_of_checks 1 0 4 slice047 (by decide +kernel) (by decide +kernel) cover047_checked
def cover048 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00144) (.leaf leaf00145)) (.leaf leaf00146))
theorem cover048_checked : FastArmCover.accepts 1 0 4 (3/160) (31/1600) 0 1 0 1 (-11584817887/4294967296) cover048=true := by
  unfold cover048
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00144_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00145_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00146_checked
    · decide +kernel
    · decide +kernel
def slice048 : Slice := ⟨cover048,(3/160),(31/1600),(-11584817887/4294967296)⟩
theorem slice048_checked : accepts 1 0 4 slice048=true :=
  accepts_of_checks 1 0 4 slice048 (by decide +kernel) (by decide +kernel) cover048_checked
def cover049 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00147) (.leaf leaf00148)) (.leaf leaf00149))
theorem cover049_checked : FastArmCover.accepts 1 0 4 (31/1600) (1/50) 0 1 0 1 (-5710947445/2147483648) cover049=true := by
  unfold cover049
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00147_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00148_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00149_checked
    · decide +kernel
    · decide +kernel
def slice049 : Slice := ⟨cover049,(31/1600),(1/50),(-5710947445/2147483648)⟩
theorem slice049_checked : accepts 1 0 4 slice049=true :=
  accepts_of_checks 1 0 4 slice049 (by decide +kernel) (by decide +kernel) cover049_checked
def cover050 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00150) (.leaf leaf00151)) (.leaf leaf00152))
theorem cover050_checked : FastArmCover.accepts 1 0 4 (1/50) (131/6400) 0 1 0 1 (-11267557563/4294967296) cover050=true := by
  unfold cover050
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00150_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00151_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00152_checked
    · decide +kernel
    · decide +kernel
def slice050 : Slice := ⟨cover050,(1/50),(131/6400),(-11267557563/4294967296)⟩
theorem slice050_checked : accepts 1 0 4 slice050=true :=
  accepts_of_checks 1 0 4 slice050 (by decide +kernel) (by decide +kernel) cover050_checked
def cover051 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00153) (.leaf leaf00154)) (.leaf leaf00155))
theorem cover051_checked : FastArmCover.accepts 1 0 4 (131/6400) (67/3200) 0 1 0 1 (-11153492637/4294967296) cover051=true := by
  unfold cover051
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00153_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00154_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00155_checked
    · decide +kernel
    · decide +kernel
def slice051 : Slice := ⟨cover051,(131/6400),(67/3200),(-11153492637/4294967296)⟩
theorem slice051_checked : accepts 1 0 4 slice051=true :=
  accepts_of_checks 1 0 4 slice051 (by decide +kernel) (by decide +kernel) cover051_checked
def cover052 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00156) (.leaf leaf00157)) (.leaf leaf00158))
theorem cover052_checked : FastArmCover.accepts 1 0 4 (67/3200) (137/6400) 0 1 0 1 (-11042453733/4294967296) cover052=true := by
  unfold cover052
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00156_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00157_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00158_checked
    · decide +kernel
    · decide +kernel
def slice052 : Slice := ⟨cover052,(67/3200),(137/6400),(-11042453733/4294967296)⟩
theorem slice052_checked : accepts 1 0 4 slice052=true :=
  accepts_of_checks 1 0 4 slice052 (by decide +kernel) (by decide +kernel) cover052_checked
def cover053 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00159) (.leaf leaf00160)) (.leaf leaf00161))
theorem cover053_checked : FastArmCover.accepts 1 0 4 (137/6400) (7/320) 0 1 0 1 (-10934295501/4294967296) cover053=true := by
  unfold cover053
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00159_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00160_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00161_checked
    · decide +kernel
    · decide +kernel
def slice053 : Slice := ⟨cover053,(137/6400),(7/320),(-10934295501/4294967296)⟩
theorem slice053_checked : accepts 1 0 4 slice053=true :=
  accepts_of_checks 1 0 4 slice053 (by decide +kernel) (by decide +kernel) cover053_checked
def cover054 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00162) (.leaf leaf00163)) (.leaf leaf00164))
theorem cover054_checked : FastArmCover.accepts 1 0 4 (7/320) (143/6400) 0 1 0 1 (-2707220577/1073741824) cover054=true := by
  unfold cover054
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00162_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00163_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00164_checked
    · decide +kernel
    · decide +kernel
def slice054 : Slice := ⟨cover054,(7/320),(143/6400),(-2707220577/1073741824)⟩
theorem slice054_checked : accepts 1 0 4 slice054=true :=
  accepts_of_checks 1 0 4 slice054 (by decide +kernel) (by decide +kernel) cover054_checked
def cover055 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00165) (.leaf leaf00166)) (.leaf leaf00167))
theorem cover055_checked : FastArmCover.accepts 1 0 4 (143/6400) (73/3200) 0 1 0 1 (-5363043647/2147483648) cover055=true := by
  unfold cover055
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00165_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00166_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00167_checked
    · decide +kernel
    · decide +kernel
def slice055 : Slice := ⟨cover055,(143/6400),(73/3200),(-5363043647/2147483648)⟩
theorem slice055_checked : accepts 1 0 4 slice055=true :=
  accepts_of_checks 1 0 4 slice055 (by decide +kernel) (by decide +kernel) cover055_checked
def cover056 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00168) (.leaf leaf00169)) (.leaf leaf00170))
theorem cover056_checked : FastArmCover.accepts 1 0 4 (73/3200) (19/800) 0 1 0 1 (-10620232379/4294967296) cover056=true := by
  unfold cover056
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00168_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00169_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00170_checked
    · decide +kernel
    · decide +kernel
def slice056 : Slice := ⟨cover056,(73/3200),(19/800),(-10620232379/4294967296)⟩
theorem slice056_checked : accepts 1 0 4 slice056=true :=
  accepts_of_checks 1 0 4 slice056 (by decide +kernel) (by decide +kernel) cover056_checked
def cover057 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00171) (.leaf leaf00172)) (.leaf leaf00173))
theorem cover057_checked : FastArmCover.accepts 1 0 4 (19/800) (79/3200) 0 1 0 1 (-5213612293/2147483648) cover057=true := by
  unfold cover057
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00171_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00172_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00173_checked
    · decide +kernel
    · decide +kernel
def slice057 : Slice := ⟨cover057,(19/800),(79/3200),(-5213612293/2147483648)⟩
theorem slice057_checked : accepts 1 0 4 slice057=true :=
  accepts_of_checks 1 0 4 slice057 (by decide +kernel) (by decide +kernel) cover057_checked
def cover058 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00174) (.leaf leaf00175)) (.leaf leaf00176))
theorem cover058_checked : FastArmCover.accepts 1 0 4 (79/3200) (41/1600) 0 1 0 1 (-5121455471/2147483648) cover058=true := by
  unfold cover058
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00174_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00175_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00176_checked
    · decide +kernel
    · decide +kernel
def slice058 : Slice := ⟨cover058,(79/3200),(41/1600),(-5121455471/2147483648)⟩
theorem slice058_checked : accepts 1 0 4 slice058=true :=
  accepts_of_checks 1 0 4 slice058 (by decide +kernel) (by decide +kernel) cover058_checked
def cover059 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00177) (.leaf leaf00178)) (.leaf leaf00179))
theorem cover059_checked : FastArmCover.accepts 1 0 4 (41/1600) (17/640) 0 1 0 1 (-10066583307/4294967296) cover059=true := by
  unfold cover059
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00177_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00178_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00179_checked
    · decide +kernel
    · decide +kernel
def slice059 : Slice := ⟨cover059,(41/1600),(17/640),(-10066583307/4294967296)⟩
theorem slice059_checked : accepts 1 0 4 slice059=true :=
  accepts_of_checks 1 0 4 slice059 (by decide +kernel) (by decide +kernel) cover059_checked
def cover060 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00180) (.leaf leaf00181)) (.leaf leaf00182))
theorem cover060_checked : FastArmCover.accepts 1 0 4 (17/640) (11/400) 0 1 0 1 (-4948806483/2147483648) cover060=true := by
  unfold cover060
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00180_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00181_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00182_checked
    · decide +kernel
    · decide +kernel
def slice060 : Slice := ⟨cover060,(17/640),(11/400),(-4948806483/2147483648)⟩
theorem slice060_checked : accepts 1 0 4 slice060=true :=
  accepts_of_checks 1 0 4 slice060 (by decide +kernel) (by decide +kernel) cover060_checked
def cover061 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00183) (.leaf leaf00184)) (.leaf leaf00185))
theorem cover061_checked : FastArmCover.accepts 1 0 4 (11/400) (91/3200) 0 1 0 1 (-9735439823/4294967296) cover061=true := by
  unfold cover061
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00183_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00184_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00185_checked
    · decide +kernel
    · decide +kernel
def slice061 : Slice := ⟨cover061,(11/400),(91/3200),(-9735439823/4294967296)⟩
theorem slice061_checked : accepts 1 0 4 slice061=true :=
  accepts_of_checks 1 0 4 slice061 (by decide +kernel) (by decide +kernel) cover061_checked
def cover062 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00186) (.leaf leaf00187)) (.leaf leaf00188))
theorem cover062_checked : FastArmCover.accepts 1 0 4 (91/3200) (47/1600) 0 1 0 1 (-9579563083/4294967296) cover062=true := by
  unfold cover062
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00186_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00187_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00188_checked
    · decide +kernel
    · decide +kernel
def slice062 : Slice := ⟨cover062,(91/3200),(47/1600),(-9579563083/4294967296)⟩
theorem slice062_checked : accepts 1 0 4 slice062=true :=
  accepts_of_checks 1 0 4 slice062 (by decide +kernel) (by decide +kernel) cover062_checked
def cover063 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00189) (.leaf leaf00190)) (.leaf leaf00191))
theorem cover063_checked : FastArmCover.accepts 1 0 4 (47/1600) (97/3200) 0 1 0 1 (-9429533357/4294967296) cover063=true := by
  unfold cover063
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00189_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00190_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00191_checked
    · decide +kernel
    · decide +kernel
def slice063 : Slice := ⟨cover063,(47/1600),(97/3200),(-9429533357/4294967296)⟩
theorem slice063_checked : accepts 1 0 4 slice063=true :=
  accepts_of_checks 1 0 4 slice063 (by decide +kernel) (by decide +kernel) cover063_checked
def cover064 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00192) (.leaf leaf00193)) (.leaf leaf00194))
theorem cover064_checked : FastArmCover.accepts 1 0 4 (97/3200) (1/32) 0 1 0 1 (-580309131/268435456) cover064=true := by
  unfold cover064
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00192_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00193_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00194_checked
    · decide +kernel
    · decide +kernel
def slice064 : Slice := ⟨cover064,(97/3200),(1/32),(-580309131/268435456)⟩
theorem slice064_checked : accepts 1 0 4 slice064=true :=
  accepts_of_checks 1 0 4 slice064 (by decide +kernel) (by decide +kernel) cover064_checked
def cover065 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00195) (.leaf leaf00196)) (.leaf leaf00197))
theorem cover065_checked : FastArmCover.accepts 1 0 4 (1/32) (103/3200) 0 1 0 1 (-9145436159/4294967296) cover065=true := by
  unfold cover065
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00195_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00196_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00197_checked
    · decide +kernel
    · decide +kernel
def slice065 : Slice := ⟨cover065,(1/32),(103/3200),(-9145436159/4294967296)⟩
theorem slice065_checked : accepts 1 0 4 slice065=true :=
  accepts_of_checks 1 0 4 slice065 (by decide +kernel) (by decide +kernel) cover065_checked
def cover066 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00198) (.leaf leaf00199)) (.leaf leaf00200))
theorem cover066_checked : FastArmCover.accepts 1 0 4 (103/3200) (53/1600) 0 1 0 1 (-1126334121/536870912) cover066=true := by
  unfold cover066
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00198_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00199_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00200_checked
    · decide +kernel
    · decide +kernel
def slice066 : Slice := ⟨cover066,(103/3200),(53/1600),(-1126334121/536870912)⟩
theorem slice066_checked : accepts 1 0 4 slice066=true :=
  accepts_of_checks 1 0 4 slice066 (by decide +kernel) (by decide +kernel) cover066_checked
def cover067 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00201) (.leaf leaf00202)) (.leaf leaf00203))
theorem cover067_checked : FastArmCover.accepts 1 0 4 (53/1600) (109/3200) 0 1 0 1 (-8880356303/4294967296) cover067=true := by
  unfold cover067
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00201_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00202_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00203_checked
    · decide +kernel
    · decide +kernel
def slice067 : Slice := ⟨cover067,(53/1600),(109/3200),(-8880356303/4294967296)⟩
theorem slice067_checked : accepts 1 0 4 slice067=true :=
  accepts_of_checks 1 0 4 slice067 (by decide +kernel) (by decide +kernel) cover067_checked
def cover068 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00204) (.leaf leaf00205)) (.leaf leaf00206))
theorem cover068_checked : FastArmCover.accepts 1 0 4 (109/3200) (7/200) 0 1 0 1 (-8754213115/4294967296) cover068=true := by
  unfold cover068
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00204_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00205_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00206_checked
    · decide +kernel
    · decide +kernel
def slice068 : Slice := ⟨cover068,(109/3200),(7/200),(-8754213115/4294967296)⟩
theorem slice068_checked : accepts 1 0 4 slice068=true :=
  accepts_of_checks 1 0 4 slice068 (by decide +kernel) (by decide +kernel) cover068_checked
def cover069 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00207) (.leaf leaf00208)) (.leaf leaf00209))
theorem cover069_checked : FastArmCover.accepts 1 0 4 (7/200) (23/640) 0 1 0 1 (-2157998551/1073741824) cover069=true := by
  unfold cover069
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00207_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00208_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00209_checked
    · decide +kernel
    · decide +kernel
def slice069 : Slice := ⟨cover069,(7/200),(23/640),(-2157998551/1073741824)⟩
theorem slice069_checked : accepts 1 0 4 slice069=true :=
  accepts_of_checks 1 0 4 slice069 (by decide +kernel) (by decide +kernel) cover069_checked
def cover070 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00210) (.leaf leaf00211)) (.leaf leaf00212))
theorem cover070_checked : FastArmCover.accepts 1 0 4 (23/640) (59/1600) 0 1 0 1 (-4256735829/2147483648) cover070=true := by
  unfold cover070
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00210_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00211_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00212_checked
    · decide +kernel
    · decide +kernel
def slice070 : Slice := ⟨cover070,(23/640),(59/1600),(-4256735829/2147483648)⟩
theorem slice070_checked : accepts 1 0 4 slice070=true :=
  accepts_of_checks 1 0 4 slice070 (by decide +kernel) (by decide +kernel) cover070_checked
def cover071 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00213) (.leaf leaf00214)) (.leaf leaf00215))
theorem cover071_checked : FastArmCover.accepts 1 0 4 (59/1600) (121/3200) 0 1 0 1 (-1049804579/536870912) cover071=true := by
  unfold cover071
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00213_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00214_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00215_checked
    · decide +kernel
    · decide +kernel
def slice071 : Slice := ⟨cover071,(59/1600),(121/3200),(-1049804579/536870912)⟩
theorem slice071_checked : accepts 1 0 4 slice071=true :=
  accepts_of_checks 1 0 4 slice071 (by decide +kernel) (by decide +kernel) cover071_checked
def cover072 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00216) (.leaf leaf00217)) (.leaf leaf00218))
theorem cover072_checked : FastArmCover.accepts 1 0 4 (121/3200) (31/800) 0 1 0 1 (-4143348677/2147483648) cover072=true := by
  unfold cover072
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00216_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00217_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00218_checked
    · decide +kernel
    · decide +kernel
def slice072 : Slice := ⟨cover072,(121/3200),(31/800),(-4143348677/2147483648)⟩
theorem slice072_checked : accepts 1 0 4 slice072=true :=
  accepts_of_checks 1 0 4 slice072 (by decide +kernel) (by decide +kernel) cover072_checked
def cover073 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00219) (.leaf leaf00220)) (.leaf leaf00221))
theorem cover073_checked : FastArmCover.accepts 1 0 4 (31/800) (127/3200) 0 1 0 1 (-8178077293/4294967296) cover073=true := by
  unfold cover073
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00219_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00220_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00221_checked
    · decide +kernel
    · decide +kernel
def slice073 : Slice := ⟨cover073,(31/800),(127/3200),(-8178077293/4294967296)⟩
theorem slice073_checked : accepts 1 0 4 slice073=true :=
  accepts_of_checks 1 0 4 slice073 (by decide +kernel) (by decide +kernel) cover073_checked
def cover074 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00222) (.leaf leaf00223)) (.leaf leaf00224))
theorem cover074_checked : FastArmCover.accepts 1 0 4 (127/3200) (13/320) 0 1 0 1 (-8072413649/4294967296) cover074=true := by
  unfold cover074
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00222_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00223_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00224_checked
    · decide +kernel
    · decide +kernel
def slice074 : Slice := ⟨cover074,(127/3200),(13/320),(-8072413649/4294967296)⟩
theorem slice074_checked : accepts 1 0 4 slice074=true :=
  accepts_of_checks 1 0 4 slice074 (by decide +kernel) (by decide +kernel) cover074_checked
def cover075 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00225) (.leaf leaf00226)) (.leaf leaf00227))
theorem cover075_checked : FastArmCover.accepts 1 0 4 (13/320) (133/3200) 0 1 0 1 (-498097253/268435456) cover075=true := by
  unfold cover075
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00225_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00226_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00227_checked
    · decide +kernel
    · decide +kernel
def slice075 : Slice := ⟨cover075,(13/320),(133/3200),(-498097253/268435456)⟩
theorem slice075_checked : accepts 1 0 4 slice075=true :=
  accepts_of_checks 1 0 4 slice075 (by decide +kernel) (by decide +kernel) cover075_checked
def cover076 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00228) (.leaf leaf00229)) (.leaf leaf00230))
theorem cover076_checked : FastArmCover.accepts 1 0 4 (133/3200) (17/400) 0 1 0 1 (-7869365343/4294967296) cover076=true := by
  unfold cover076
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00228_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00229_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00230_checked
    · decide +kernel
    · decide +kernel
def slice076 : Slice := ⟨cover076,(133/3200),(17/400),(-7869365343/4294967296)⟩
theorem slice076_checked : accepts 1 0 4 slice076=true :=
  accepts_of_checks 1 0 4 slice076 (by decide +kernel) (by decide +kernel) cover076_checked
def cover077 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00231) (.leaf leaf00232)) (.leaf leaf00233))
theorem cover077_checked : FastArmCover.accepts 1 0 4 (17/400) (139/3200) 0 1 0 1 (-7771712461/4294967296) cover077=true := by
  unfold cover077
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00231_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00232_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00233_checked
    · decide +kernel
    · decide +kernel
def slice077 : Slice := ⟨cover077,(17/400),(139/3200),(-7771712461/4294967296)⟩
theorem slice077_checked : accepts 1 0 4 slice077=true :=
  accepts_of_checks 1 0 4 slice077 (by decide +kernel) (by decide +kernel) cover077_checked
def cover078 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00234) (.leaf leaf00235)) (.leaf leaf00236))
theorem cover078_checked : FastArmCover.accepts 1 0 4 (139/3200) (71/1600) 0 1 0 1 (-7676477581/4294967296) cover078=true := by
  unfold cover078
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00234_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00235_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00236_checked
    · decide +kernel
    · decide +kernel
def slice078 : Slice := ⟨cover078,(139/3200),(71/1600),(-7676477581/4294967296)⟩
theorem slice078_checked : accepts 1 0 4 slice078=true :=
  accepts_of_checks 1 0 4 slice078 (by decide +kernel) (by decide +kernel) cover078_checked
def cover079 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00237) (.leaf leaf00238)) (.leaf leaf00239))
theorem cover079_checked : FastArmCover.accepts 1 0 4 (71/1600) (29/640) 0 1 0 1 (-947943651/536870912) cover079=true := by
  unfold cover079
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00237_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00238_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00239_checked
    · decide +kernel
    · decide +kernel
def slice079 : Slice := ⟨cover079,(71/1600),(29/640),(-947943651/536870912)⟩
theorem slice079_checked : accepts 1 0 4 slice079=true :=
  accepts_of_checks 1 0 4 slice079 (by decide +kernel) (by decide +kernel) cover079_checked
def cover080 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00240) (.leaf leaf00241)) (.leaf leaf00242))
theorem cover080_checked : FastArmCover.accepts 1 0 4 (29/640) (37/800) 0 1 0 1 (-7492823469/4294967296) cover080=true := by
  unfold cover080
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00240_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00241_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00242_checked
    · decide +kernel
    · decide +kernel
def slice080 : Slice := ⟨cover080,(29/640),(37/800),(-7492823469/4294967296)⟩
theorem slice080_checked : accepts 1 0 4 slice080=true :=
  accepts_of_checks 1 0 4 slice080 (by decide +kernel) (by decide +kernel) cover080_checked
def cover081 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00243) (.leaf leaf00244)) (.leaf leaf00245))
theorem cover081_checked : FastArmCover.accepts 1 0 4 (37/800) (151/3200) 0 1 0 1 (-7404203437/4294967296) cover081=true := by
  unfold cover081
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00243_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00244_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00245_checked
    · decide +kernel
    · decide +kernel
def slice081 : Slice := ⟨cover081,(37/800),(151/3200),(-7404203437/4294967296)⟩
theorem slice081_checked : accepts 1 0 4 slice081=true :=
  accepts_of_checks 1 0 4 slice081 (by decide +kernel) (by decide +kernel) cover081_checked
def cover082 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00246) (.leaf leaf00247)) (.leaf leaf00248))
theorem cover082_checked : FastArmCover.accepts 1 0 4 (151/3200) (77/1600) 0 1 0 1 (-1829399655/1073741824) cover082=true := by
  unfold cover082
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00246_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00247_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00248_checked
    · decide +kernel
    · decide +kernel
def slice082 : Slice := ⟨cover082,(151/3200),(77/1600),(-1829399655/1073741824)⟩
theorem slice082_checked : accepts 1 0 4 slice082=true :=
  accepts_of_checks 1 0 4 slice082 (by decide +kernel) (by decide +kernel) cover082_checked
def cover083 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00249) (.leaf leaf00250)) (.leaf leaf00251))
theorem cover083_checked : FastArmCover.accepts 1 0 4 (77/1600) (1/20) 0 1 0 1 (-7231771849/4294967296) cover083=true := by
  unfold cover083
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00249_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00250_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00251_checked
    · decide +kernel
    · decide +kernel
def slice083 : Slice := ⟨cover083,(77/1600),(1/20),(-7231771849/4294967296)⟩
theorem slice083_checked : accepts 1 0 4 slice083=true :=
  accepts_of_checks 1 0 4 slice083 (by decide +kernel) (by decide +kernel) cover083_checked
def cover084 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00252) (.leaf leaf00253)) (.leaf leaf00254))
theorem cover084_checked : FastArmCover.accepts 1 0 4 (1/20) (33/640) 0 1 0 1 (-3534192649/2147483648) cover084=true := by
  unfold cover084
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00252_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00253_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00254_checked
    · decide +kernel
    · decide +kernel
def slice084 : Slice := ⟨cover084,(1/20),(33/640),(-3534192649/2147483648)⟩
theorem slice084_checked : accepts 1 0 4 slice084=true :=
  accepts_of_checks 1 0 4 slice084 (by decide +kernel) (by decide +kernel) cover084_checked
def cover085 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00255) (.leaf leaf00256)) (.leaf leaf00257))
theorem cover085_checked : FastArmCover.accepts 1 0 4 (33/640) (17/320) 0 1 0 1 (-1734285555/1073741824) cover085=true := by
  unfold cover085
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00255_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00256_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00257_checked
    · decide +kernel
    · decide +kernel
def slice085 : Slice := ⟨cover085,(33/640),(17/320),(-1734285555/1073741824)⟩
theorem slice085_checked : accepts 1 0 4 slice085=true :=
  accepts_of_checks 1 0 4 slice085 (by decide +kernel) (by decide +kernel) cover085_checked
def cover086 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00258) (.leaf leaf00259)) (.leaf leaf00260))
theorem cover086_checked : FastArmCover.accepts 1 0 4 (17/320) (7/128) 0 1 0 1 (-6810333335/4294967296) cover086=true := by
  unfold cover086
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00258_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00259_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00260_checked
    · decide +kernel
    · decide +kernel
def slice086 : Slice := ⟨cover086,(17/320),(7/128),(-6810333335/4294967296)⟩
theorem slice086_checked : accepts 1 0 4 slice086=true :=
  accepts_of_checks 1 0 4 slice086 (by decide +kernel) (by decide +kernel) cover086_checked
def cover087 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00261) (.leaf leaf00262)) (.leaf leaf00263))
theorem cover087_checked : FastArmCover.accepts 1 0 4 (7/128) (9/160) 0 1 0 1 (-6687688803/4294967296) cover087=true := by
  unfold cover087
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00261_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00262_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00263_checked
    · decide +kernel
    · decide +kernel
def slice087 : Slice := ⟨cover087,(7/128),(9/160),(-6687688803/4294967296)⟩
theorem slice087_checked : accepts 1 0 4 slice087=true :=
  accepts_of_checks 1 0 4 slice087 (by decide +kernel) (by decide +kernel) cover087_checked
def cover088 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00264) (.leaf leaf00265)) (.leaf leaf00266))
theorem cover088_checked : FastArmCover.accepts 1 0 4 (9/160) (37/640) 0 1 0 1 (-821120415/536870912) cover088=true := by
  unfold cover088
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00264_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00265_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00266_checked
    · decide +kernel
    · decide +kernel
def slice088 : Slice := ⟨cover088,(9/160),(37/640),(-821120415/536870912)⟩
theorem slice088_checked : accepts 1 0 4 slice088=true :=
  accepts_of_checks 1 0 4 slice088 (by decide +kernel) (by decide +kernel) cover088_checked
def cover089 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00267) (.leaf leaf00268)) (.leaf leaf00269))
theorem cover089_checked : FastArmCover.accepts 1 0 4 (37/640) (19/320) 0 1 0 1 (-3226966607/2147483648) cover089=true := by
  unfold cover089
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00267_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00268_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00269_checked
    · decide +kernel
    · decide +kernel
def slice089 : Slice := ⟨cover089,(37/640),(19/320),(-3226966607/2147483648)⟩
theorem slice089_checked : accepts 1 0 4 slice089=true :=
  accepts_of_checks 1 0 4 slice089 (by decide +kernel) (by decide +kernel) cover089_checked
def cover090 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00270) (.leaf leaf00271)) (.leaf leaf00272))
theorem cover090_checked : FastArmCover.accepts 1 0 4 (19/320) (39/640) 0 1 0 1 (-3171197005/2147483648) cover090=true := by
  unfold cover090
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00270_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00271_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00272_checked
    · decide +kernel
    · decide +kernel
def slice090 : Slice := ⟨cover090,(19/320),(39/640),(-3171197005/2147483648)⟩
theorem slice090_checked : accepts 1 0 4 slice090=true :=
  accepts_of_checks 1 0 4 slice090 (by decide +kernel) (by decide +kernel) cover090_checked
def cover091 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00273) (.leaf leaf00274)) (.leaf leaf00275))
theorem cover091_checked : FastArmCover.accepts 1 0 4 (39/640) (1/16) 0 1 0 1 (-6234158225/4294967296) cover091=true := by
  unfold cover091
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00273_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00274_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00275_checked
    · decide +kernel
    · decide +kernel
def slice091 : Slice := ⟨cover091,(39/640),(1/16),(-6234158225/4294967296)⟩
theorem slice091_checked : accepts 1 0 4 slice091=true :=
  accepts_of_checks 1 0 4 slice091 (by decide +kernel) (by decide +kernel) cover091_checked
def cover092 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00276) (.leaf leaf00277)) (.leaf leaf00278))
theorem cover092_checked : FastArmCover.accepts 1 0 4 (1/16) (41/640) 0 1 0 1 (-1532263393/1073741824) cover092=true := by
  unfold cover092
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00276_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00277_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00278_checked
    · decide +kernel
    · decide +kernel
def slice092 : Slice := ⟨cover092,(1/16),(41/640),(-1532263393/1073741824)⟩
theorem slice092_checked : accepts 1 0 4 slice092=true :=
  accepts_of_checks 1 0 4 slice092 (by decide +kernel) (by decide +kernel) cover092_checked
def cover093 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00279) (.leaf leaf00280)) (.leaf leaf00281))
theorem cover093_checked : FastArmCover.accepts 1 0 4 (41/640) (21/320) 0 1 0 1 (-6026921317/4294967296) cover093=true := by
  unfold cover093
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00279_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00280_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00281_checked
    · decide +kernel
    · decide +kernel
def slice093 : Slice := ⟨cover093,(41/640),(21/320),(-6026921317/4294967296)⟩
theorem slice093_checked : accepts 1 0 4 slice093=true :=
  accepts_of_checks 1 0 4 slice093 (by decide +kernel) (by decide +kernel) cover093_checked
def cover094 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00282) (.leaf leaf00283)) (.leaf leaf00284))
theorem cover094_checked : FastArmCover.accepts 1 0 4 (21/320) (43/640) 0 1 0 1 (-5927614865/4294967296) cover094=true := by
  unfold cover094
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00282_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00283_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00284_checked
    · decide +kernel
    · decide +kernel
def slice094 : Slice := ⟨cover094,(21/320),(43/640),(-5927614865/4294967296)⟩
theorem slice094_checked : accepts 1 0 4 slice094=true :=
  accepts_of_checks 1 0 4 slice094 (by decide +kernel) (by decide +kernel) cover094_checked
def cover095 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00285) (.leaf leaf00286)) (.leaf leaf00287))
theorem cover095_checked : FastArmCover.accepts 1 0 4 (43/640) (11/160) 0 1 0 1 (-5830998643/4294967296) cover095=true := by
  unfold cover095
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00285_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00286_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00287_checked
    · decide +kernel
    · decide +kernel
def slice095 : Slice := ⟨cover095,(43/640),(11/160),(-5830998643/4294967296)⟩
theorem slice095_checked : accepts 1 0 4 slice095=true :=
  accepts_of_checks 1 0 4 slice095 (by decide +kernel) (by decide +kernel) cover095_checked
def cover096 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00288) (.leaf leaf00289)) (.leaf leaf00290))
theorem cover096_checked : FastArmCover.accepts 1 0 4 (11/160) (23/320) 0 1 0 1 (-717074565/536870912) cover096=true := by
  unfold cover096
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00288_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00289_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00290_checked
    · decide +kernel
    · decide +kernel
def slice096 : Slice := ⟨cover096,(11/160),(23/320),(-717074565/536870912)⟩
theorem slice096_checked : accepts 1 0 4 slice096=true :=
  accepts_of_checks 1 0 4 slice096 (by decide +kernel) (by decide +kernel) cover096_checked
def cover097 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00291) (.leaf leaf00292)) (.leaf leaf00293))
theorem cover097_checked : FastArmCover.accepts 1 0 4 (23/320) (3/40) 0 1 0 1 (-347238861/268435456) cover097=true := by
  unfold cover097
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00291_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00292_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00293_checked
    · decide +kernel
    · decide +kernel
def slice097 : Slice := ⟨cover097,(23/320),(3/40),(-347238861/268435456)⟩
theorem slice097_checked : accepts 1 0 4 slice097=true :=
  accepts_of_checks 1 0 4 slice097 (by decide +kernel) (by decide +kernel) cover097_checked
def cover098 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00294) (.leaf leaf00295)) (.leaf leaf00296))
theorem cover098_checked : FastArmCover.accepts 1 0 4 (3/40) (5/64) 0 1 0 1 (-5383986785/4294967296) cover098=true := by
  unfold cover098
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00294_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00295_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00296_checked
    · decide +kernel
    · decide +kernel
def slice098 : Slice := ⟨cover098,(3/40),(5/64),(-5383986785/4294967296)⟩
theorem slice098_checked : accepts 1 0 4 slice098=true :=
  accepts_of_checks 1 0 4 slice098 (by decide +kernel) (by decide +kernel) cover098_checked
def cover099 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00297) (.leaf leaf00298)) (.leaf leaf00299))
theorem cover099_checked : FastArmCover.accepts 1 0 4 (5/64) (13/160) 0 1 0 1 (-5220359645/4294967296) cover099=true := by
  unfold cover099
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00297_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00298_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00299_checked
    · decide +kernel
    · decide +kernel
def slice099 : Slice := ⟨cover099,(5/64),(13/160),(-5220359645/4294967296)⟩
theorem slice099_checked : accepts 1 0 4 slice099=true :=
  accepts_of_checks 1 0 4 slice099 (by decide +kernel) (by decide +kernel) cover099_checked
def cover100 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00300) (.leaf leaf00301)) (.leaf leaf00302))
theorem cover100_checked : FastArmCover.accepts 1 0 4 (13/160) (27/320) 0 1 0 1 (-5064297257/4294967296) cover100=true := by
  unfold cover100
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00300_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00301_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00302_checked
    · decide +kernel
    · decide +kernel
def slice100 : Slice := ⟨cover100,(13/160),(27/320),(-5064297257/4294967296)⟩
theorem slice100_checked : accepts 1 0 4 slice100=true :=
  accepts_of_checks 1 0 4 slice100 (by decide +kernel) (by decide +kernel) cover100_checked
def cover101 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00303) (.leaf leaf00304)) (.leaf leaf00305))
theorem cover101_checked : FastArmCover.accepts 1 0 4 (27/320) (7/80) 0 1 0 1 (-153600975/134217728) cover101=true := by
  unfold cover101
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00303_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00304_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00305_checked
    · decide +kernel
    · decide +kernel
def slice101 : Slice := ⟨cover101,(27/320),(7/80),(-153600975/134217728)⟩
theorem slice101_checked : accepts 1 0 4 slice101=true :=
  accepts_of_checks 1 0 4 slice101 (by decide +kernel) (by decide +kernel) cover101_checked
def cover102 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00306) (.leaf leaf00307)) (.leaf leaf00308))
theorem cover102_checked : FastArmCover.accepts 1 0 4 (7/80) (29/320) 0 1 0 1 (-4772656335/4294967296) cover102=true := by
  unfold cover102
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00306_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00307_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00308_checked
    · decide +kernel
    · decide +kernel
def slice102 : Slice := ⟨cover102,(7/80),(29/320),(-4772656335/4294967296)⟩
theorem slice102_checked : accepts 1 0 4 slice102=true :=
  accepts_of_checks 1 0 4 slice102 (by decide +kernel) (by decide +kernel) cover102_checked
def cover103 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00309) (.leaf leaf00310)) (.leaf leaf00311))
theorem cover103_checked : FastArmCover.accepts 1 0 4 (29/320) (3/32) 0 1 0 1 (-4636121499/4294967296) cover103=true := by
  unfold cover103
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00309_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00310_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00311_checked
    · decide +kernel
    · decide +kernel
def slice103 : Slice := ⟨cover103,(29/320),(3/32),(-4636121499/4294967296)⟩
theorem slice103_checked : accepts 1 0 4 slice103=true :=
  accepts_of_checks 1 0 4 slice103 (by decide +kernel) (by decide +kernel) cover103_checked
def cover104 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00312) (.leaf leaf00313)) (.leaf leaf00314))
theorem cover104_checked : FastArmCover.accepts 1 0 4 (3/32) (31/320) 0 1 0 1 (-2252610935/2147483648) cover104=true := by
  unfold cover104
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00312_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00313_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00314_checked
    · decide +kernel
    · decide +kernel
def slice104 : Slice := ⟨cover104,(3/32),(31/320),(-2252610935/2147483648)⟩
theorem slice104_checked : accepts 1 0 4 slice104=true :=
  accepts_of_checks 1 0 4 slice104 (by decide +kernel) (by decide +kernel) cover104_checked
def cover105 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00315) (.leaf leaf00316)) (.leaf leaf00317))
theorem cover105_checked : FastArmCover.accepts 1 0 4 (31/320) (1/10) 0 1 0 1 (-1094898147/1073741824) cover105=true := by
  unfold cover105
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00315_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00316_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00317_checked
    · decide +kernel
    · decide +kernel
def slice105 : Slice := ⟨cover105,(31/320),(1/10),(-1094898147/1073741824)⟩
theorem slice105_checked : accepts 1 0 4 slice105=true :=
  accepts_of_checks 1 0 4 slice105 (by decide +kernel) (by decide +kernel) cover105_checked
def cover106 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00318) (.leaf leaf00319)) (.leaf leaf00320))
theorem cover106_checked : FastArmCover.accepts 1 0 4 (1/10) (33/320) 0 1 0 1 (-2129451833/2147483648) cover106=true := by
  unfold cover106
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00318_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00319_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00320_checked
    · decide +kernel
    · decide +kernel
def slice106 : Slice := ⟨cover106,(1/10),(33/320),(-2129451833/2147483648)⟩
theorem slice106_checked : accepts 1 0 4 slice106=true :=
  accepts_of_checks 1 0 4 slice106 (by decide +kernel) (by decide +kernel) cover106_checked
def cover107 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00321) (.leaf leaf00322)) (.leaf leaf00323))
theorem cover107_checked : FastArmCover.accepts 1 0 4 (33/320) (17/160) 0 1 0 1 (-2071427661/2147483648) cover107=true := by
  unfold cover107
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00321_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00322_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00323_checked
    · decide +kernel
    · decide +kernel
def slice107 : Slice := ⟨cover107,(33/320),(17/160),(-2071427661/2147483648)⟩
theorem slice107_checked : accepts 1 0 4 slice107=true :=
  accepts_of_checks 1 0 4 slice107 (by decide +kernel) (by decide +kernel) cover107_checked
def cover108 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00324) (.leaf leaf00325)) (.leaf leaf00326))
theorem cover108_checked : FastArmCover.accepts 1 0 4 (17/160) (9/80) 0 1 0 1 (-4031529971/4294967296) cover108=true := by
  unfold cover108
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00324_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00325_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00326_checked
    · decide +kernel
    · decide +kernel
def slice108 : Slice := ⟨cover108,(17/160),(9/80),(-4031529971/4294967296)⟩
theorem slice108_checked : accepts 1 0 4 slice108=true :=
  accepts_of_checks 1 0 4 slice108 (by decide +kernel) (by decide +kernel) cover108_checked
def cover109 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00327) (.leaf leaf00328)) (.leaf leaf00329))
theorem cover109_checked : FastArmCover.accepts 1 0 4 (9/80) (19/160) 0 1 0 1 (-119385567/134217728) cover109=true := by
  unfold cover109
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00327_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00328_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00329_checked
    · decide +kernel
    · decide +kernel
def slice109 : Slice := ⟨cover109,(9/80),(19/160),(-119385567/134217728)⟩
theorem slice109_checked : accepts 1 0 4 slice109=true :=
  accepts_of_checks 1 0 4 slice109 (by decide +kernel) (by decide +kernel) cover109_checked
def cover110 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00330) (.leaf leaf00331)) (.leaf leaf00332))
theorem cover110_checked : FastArmCover.accepts 1 0 4 (19/160) (1/8) 0 1 0 1 (-3623862361/4294967296) cover110=true := by
  unfold cover110
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00330_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00331_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00332_checked
    · decide +kernel
    · decide +kernel
def slice110 : Slice := ⟨cover110,(19/160),(1/8),(-3623862361/4294967296)⟩
theorem slice110_checked : accepts 1 0 4 slice110=true :=
  accepts_of_checks 1 0 4 slice110 (by decide +kernel) (by decide +kernel) cover110_checked
def cover111 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00333) (.leaf leaf00334)) (.leaf leaf00335))
theorem cover111_checked : FastArmCover.accepts 1 0 4 (1/8) (21/160) 0 1 0 1 (-3440607999/4294967296) cover111=true := by
  unfold cover111
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00333_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00334_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00335_checked
    · decide +kernel
    · decide +kernel
def slice111 : Slice := ⟨cover111,(1/8),(21/160),(-3440607999/4294967296)⟩
theorem slice111_checked : accepts 1 0 4 slice111=true :=
  accepts_of_checks 1 0 4 slice111 (by decide +kernel) (by decide +kernel) cover111_checked
def cover112 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00336) (.leaf leaf00337)) (.leaf leaf00338))
theorem cover112_checked : FastArmCover.accepts 1 0 4 (21/160) (11/80) 0 1 0 1 (-817323077/1073741824) cover112=true := by
  unfold cover112
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00336_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00337_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00338_checked
    · decide +kernel
    · decide +kernel
def slice112 : Slice := ⟨cover112,(21/160),(11/80),(-817323077/1073741824)⟩
theorem slice112_checked : accepts 1 0 4 slice112=true :=
  accepts_of_checks 1 0 4 slice112 (by decide +kernel) (by decide +kernel) cover112_checked
def cover113 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00339) (.leaf leaf00340)) (.leaf leaf00341))
theorem cover113_checked : FastArmCover.accepts 1 0 4 (11/80) (23/160) 0 1 0 1 (-3108804951/4294967296) cover113=true := by
  unfold cover113
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00339_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00340_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00341_checked
    · decide +kernel
    · decide +kernel
def slice113 : Slice := ⟨cover113,(11/80),(23/160),(-3108804951/4294967296)⟩
theorem slice113_checked : accepts 1 0 4 slice113=true :=
  accepts_of_checks 1 0 4 slice113 (by decide +kernel) (by decide +kernel) cover113_checked
def cover114 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00342) (.leaf leaf00343)) (.leaf leaf00344))
theorem cover114_checked : FastArmCover.accepts 1 0 4 (23/160) (3/20) 0 1 0 1 (-1479088745/2147483648) cover114=true := by
  unfold cover114
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00342_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00343_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00344_checked
    · decide +kernel
    · decide +kernel
def slice114 : Slice := ⟨cover114,(23/160),(3/20),(-1479088745/2147483648)⟩
theorem slice114_checked : accepts 1 0 4 slice114=true :=
  accepts_of_checks 1 0 4 slice114 (by decide +kernel) (by decide +kernel) cover114_checked
def cover115 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00345) (.leaf leaf00346)) (.leaf leaf00347))
theorem cover115_checked : FastArmCover.accepts 1 0 4 (3/20) (13/80) 0 1 0 1 (-2817572321/4294967296) cover115=true := by
  unfold cover115
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00345_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00346_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00347_checked
    · decide +kernel
    · decide +kernel
def slice115 : Slice := ⟨cover115,(3/20),(13/80),(-2817572321/4294967296)⟩
theorem slice115_checked : accepts 1 0 4 slice115=true :=
  accepts_of_checks 1 0 4 slice115 (by decide +kernel) (by decide +kernel) cover115_checked
def cover116 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00348) (.leaf leaf00349)) (.leaf leaf00350))
theorem cover116_checked : FastArmCover.accepts 1 0 4 (13/80) (7/40) 0 1 0 1 (-1279213433/2147483648) cover116=true := by
  unfold cover116
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00348_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00349_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00350_checked
    · decide +kernel
    · decide +kernel
def slice116 : Slice := ⟨cover116,(13/80),(7/40),(-1279213433/2147483648)⟩
theorem slice116_checked : accepts 1 0 4 slice116=true :=
  accepts_of_checks 1 0 4 slice116 (by decide +kernel) (by decide +kernel) cover116_checked
def cover117 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00351) (.leaf leaf00352)) (.leaf leaf00353))
theorem cover117_checked : FastArmCover.accepts 1 0 4 (7/40) (3/16) 0 1 0 1 (-2327311535/4294967296) cover117=true := by
  unfold cover117
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00351_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00352_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00353_checked
    · decide +kernel
    · decide +kernel
def slice117 : Slice := ⟨cover117,(7/40),(3/16),(-2327311535/4294967296)⟩
theorem slice117_checked : accepts 1 0 4 slice117=true :=
  accepts_of_checks 1 0 4 slice117 (by decide +kernel) (by decide +kernel) cover117_checked
def cover118 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00354) (.leaf leaf00355)) (.leaf leaf00356))
theorem cover118_checked : FastArmCover.accepts 1 0 4 (3/16) (1/5) 0 1 0 1 (-1060080949/2147483648) cover118=true := by
  unfold cover118
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00354_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00355_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00356_checked
    · decide +kernel
    · decide +kernel
def slice118 : Slice := ⟨cover118,(3/16),(1/5),(-1060080949/2147483648)⟩
theorem slice118_checked : accepts 1 0 4 slice118=true :=
  accepts_of_checks 1 0 4 slice118 (by decide +kernel) (by decide +kernel) cover118_checked
def cover119 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00357) (.leaf leaf00358)) (.leaf leaf00359))
theorem cover119_checked : FastArmCover.accepts 1 0 4 (1/5) (7/32) 0 1 0 1 (-1934589469/4294967296) cover119=true := by
  unfold cover119
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00357_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00358_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00359_checked
    · decide +kernel
    · decide +kernel
def slice119 : Slice := ⟨cover119,(1/5),(7/32),(-1934589469/4294967296)⟩
theorem slice119_checked : accepts 1 0 4 slice119=true :=
  accepts_of_checks 1 0 4 slice119 (by decide +kernel) (by decide +kernel) cover119_checked
def cover120 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00360) (.leaf leaf00361)) (.leaf leaf00362))
theorem cover120_checked : FastArmCover.accepts 1 0 4 (7/32) (19/80) 0 1 0 1 (-1687633379/4294967296) cover120=true := by
  unfold cover120
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00360_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00361_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00362_checked
    · decide +kernel
    · decide +kernel
def slice120 : Slice := ⟨cover120,(7/32),(19/80),(-1687633379/4294967296)⟩
theorem slice120_checked : accepts 1 0 4 slice120=true :=
  accepts_of_checks 1 0 4 slice120 (by decide +kernel) (by decide +kernel) cover120_checked
def cover121 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00363) (.leaf leaf00364)) (.leaf leaf00365))
theorem cover121_checked : FastArmCover.accepts 1 0 4 (19/80) (41/160) 0 1 0 1 (-1473687557/4294967296) cover121=true := by
  unfold cover121
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00363_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00364_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00365_checked
    · decide +kernel
    · decide +kernel
def slice121 : Slice := ⟨cover121,(19/80),(41/160),(-1473687557/4294967296)⟩
theorem slice121_checked : accepts 1 0 4 slice121=true :=
  accepts_of_checks 1 0 4 slice121 (by decide +kernel) (by decide +kernel) cover121_checked
def cover122 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00366) (.leaf leaf00367)) (.leaf leaf00368))
theorem cover122_checked : FastArmCover.accepts 1 0 4 (41/160) (11/40) 0 1 0 1 (-160875601/536870912) cover122=true := by
  unfold cover122
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00366_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00367_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00368_checked
    · decide +kernel
    · decide +kernel
def slice122 : Slice := ⟨cover122,(41/160),(11/40),(-160875601/536870912)⟩
theorem slice122_checked : accepts 1 0 4 slice122=true :=
  accepts_of_checks 1 0 4 slice122 (by decide +kernel) (by decide +kernel) cover122_checked
def cover123 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00369) (.leaf leaf00370)) (.leaf leaf00371))
theorem cover123_checked : FastArmCover.accepts 1 0 4 (11/40) (5/16) 0 1 0 1 (-562599303/2147483648) cover123=true := by
  unfold cover123
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00369_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00370_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00371_checked
    · decide +kernel
    · decide +kernel
def slice123 : Slice := ⟨cover123,(11/40),(5/16),(-562599303/2147483648)⟩
theorem slice123_checked : accepts 1 0 4 slice123=true :=
  accepts_of_checks 1 0 4 slice123 (by decide +kernel) (by decide +kernel) cover123_checked
def cover124 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00372) (.leaf leaf00373)) (.leaf leaf00374))
theorem cover124_checked : FastArmCover.accepts 1 0 4 (5/16) (7/20) 0 1 0 1 (-851301935/4294967296) cover124=true := by
  unfold cover124
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00372_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00373_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00374_checked
    · decide +kernel
    · decide +kernel
def slice124 : Slice := ⟨cover124,(5/16),(7/20),(-851301935/4294967296)⟩
theorem slice124_checked : accepts 1 0 4 slice124=true :=
  accepts_of_checks 1 0 4 slice124 (by decide +kernel) (by decide +kernel) cover124_checked
def cover125 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00375) (.leaf leaf00376)) (.leaf leaf00377))
theorem cover125_checked : FastArmCover.accepts 1 0 4 (7/20) (31/80) 0 1 0 1 (-633151259/4294967296) cover125=true := by
  unfold cover125
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00375_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00376_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00377_checked
    · decide +kernel
    · decide +kernel
def slice125 : Slice := ⟨cover125,(7/20),(31/80),(-633151259/4294967296)⟩
theorem slice125_checked : accepts 1 0 4 slice125=true :=
  accepts_of_checks 1 0 4 slice125 (by decide +kernel) (by decide +kernel) cover125_checked
def cover126 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00378) (.leaf leaf00379)) (.leaf leaf00380))
theorem cover126_checked : FastArmCover.accepts 1 0 4 (31/80) (17/40) 0 1 0 1 (-456295023/4294967296) cover126=true := by
  unfold cover126
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00378_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00379_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00380_checked
    · decide +kernel
    · decide +kernel
def slice126 : Slice := ⟨cover126,(31/80),(17/40),(-456295023/4294967296)⟩
theorem slice126_checked : accepts 1 0 4 slice126=true :=
  accepts_of_checks 1 0 4 slice126 (by decide +kernel) (by decide +kernel) cover126_checked
def cover127 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00381) (.leaf leaf00382)) (.leaf leaf00383))
theorem cover127_checked : FastArmCover.accepts 1 0 4 (17/40) (37/80) 0 1 0 1 (-38841647/536870912) cover127=true := by
  unfold cover127
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00381_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00382_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00383_checked
    · decide +kernel
    · decide +kernel
def slice127 : Slice := ⟨cover127,(17/40),(37/80),(-38841647/536870912)⟩
theorem slice127_checked : accepts 1 0 4 slice127=true :=
  accepts_of_checks 1 0 4 slice127 (by decide +kernel) (by decide +kernel) cover127_checked
def cover128 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00384) (.leaf leaf00385)) (.leaf leaf00386))
theorem cover128_checked : FastArmCover.accepts 1 0 4 (37/80) (1/2) 0 1 0 1 (-189386183/4294967296) cover128=true := by
  unfold cover128
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00384_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00385_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00386_checked
    · decide +kernel
    · decide +kernel
def slice128 : Slice := ⟨cover128,(37/80),(1/2),(-189386183/4294967296)⟩
theorem slice128_checked : accepts 1 0 4 slice128=true :=
  accepts_of_checks 1 0 4 slice128 (by decide +kernel) (by decide +kernel) cover128_checked
def cover129 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00387) (.second (3/4) (.leaf leaf00388) (.leaf leaf00389)))
theorem cover129_checked : FastArmCover.accepts 1 0 4 (1/2) (9/16) 0 1 0 1 (-45799585/2147483648) cover129=true := by
  unfold cover129
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00387_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00388_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00389_checked
      · decide +kernel
      · decide +kernel
def slice129 : Slice := ⟨cover129,(1/2),(9/16),(-45799585/2147483648)⟩
theorem slice129_checked : accepts 1 0 4 slice129=true :=
  accepts_of_checks 1 0 4 slice129 (by decide +kernel) (by decide +kernel) cover129_checked
def cover130 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00390) (.second (3/4) (.leaf leaf00391) (.leaf leaf00392)))
theorem cover130_checked : FastArmCover.accepts 1 0 4 (9/16) (5/8) 0 1 0 1 (34578519/4294967296) cover130=true := by
  unfold cover130
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00390_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00391_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00392_checked
      · decide +kernel
      · decide +kernel
def slice130 : Slice := ⟨cover130,(9/16),(5/8),(34578519/4294967296)⟩
theorem slice130_checked : accepts 1 0 4 slice130=true :=
  accepts_of_checks 1 0 4 slice130 (by decide +kernel) (by decide +kernel) cover130_checked
def cover131 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00393) (.second (3/4) (.leaf leaf00394) (.leaf leaf00395)))
theorem cover131_checked : FastArmCover.accepts 1 0 4 (5/8) (11/16) 0 1 0 1 (138705773/4294967296) cover131=true := by
  unfold cover131
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00393_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00394_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00395_checked
      · decide +kernel
      · decide +kernel
def slice131 : Slice := ⟨cover131,(5/8),(11/16),(138705773/4294967296)⟩
theorem slice131_checked : accepts 1 0 4 slice131=true :=
  accepts_of_checks 1 0 4 slice131 (by decide +kernel) (by decide +kernel) cover131_checked
def cover132 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00396) (.second (3/4) (.leaf leaf00397) (.leaf leaf00398)))
theorem cover132_checked : FastArmCover.accepts 1 0 4 (11/16) (3/4) 0 1 0 1 (111834149/2147483648) cover132=true := by
  unfold cover132
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00396_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00397_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00398_checked
      · decide +kernel
      · decide +kernel
def slice132 : Slice := ⟨cover132,(11/16),(3/4),(111834149/2147483648)⟩
theorem slice132_checked : accepts 1 0 4 slice132=true :=
  accepts_of_checks 1 0 4 slice132 (by decide +kernel) (by decide +kernel) cover132_checked
def cover133 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00399) (.second (3/4) (.leaf leaf00400) (.leaf leaf00401)))
theorem cover133_checked : FastArmCover.accepts 1 0 4 (3/4) (7/8) 0 1 0 1 (145242691/2147483648) cover133=true := by
  unfold cover133
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00399_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00400_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00401_checked
      · decide +kernel
      · decide +kernel
def slice133 : Slice := ⟨cover133,(3/4),(7/8),(145242691/2147483648)⟩
theorem slice133_checked : accepts 1 0 4 slice133=true :=
  accepts_of_checks 1 0 4 slice133 (by decide +kernel) (by decide +kernel) cover133_checked
def cover134 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00402) (.second (3/4) (.leaf leaf00403) (.leaf leaf00404)))
theorem cover134_checked : FastArmCover.accepts 1 0 4 (7/8) 1 0 1 0 1 (427651533388984669033/4722366482869645213696) cover134=true := by
  unfold cover134
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00402_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00403_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00404_checked
      · decide +kernel
      · decide +kernel
def slice134 : Slice := ⟨cover134,(7/8),1,(427651533388984669033/4722366482869645213696)⟩
theorem slice134_checked : accepts 1 0 4 slice134=true :=
  accepts_of_checks 1 0 4 slice134 (by decide +kernel) (by decide +kernel) cover134_checked
def cover135 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00405) (.second (3/4) (.leaf leaf00406) (.leaf leaf00407)))
theorem cover135_checked : FastArmCover.accepts 1 0 4 1 (8/7) 0 1 0 1 (448569157/4294967296) cover135=true := by
  unfold cover135
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00405_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00406_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00407_checked
      · decide +kernel
      · decide +kernel
def slice135 : Slice := ⟨cover135,1,(8/7),(448569157/4294967296)⟩
theorem slice135_checked : accepts 1 0 4 slice135=true :=
  accepts_of_checks 1 0 4 slice135 (by decide +kernel) (by decide +kernel) cover135_checked
def cover136 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00408) (.second (3/4) (.leaf leaf00409) (.leaf leaf00410)))
theorem cover136_checked : FastArmCover.accepts 1 0 4 (8/7) (4/3) 0 1 0 1 (241867005/2147483648) cover136=true := by
  unfold cover136
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00408_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00409_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00410_checked
      · decide +kernel
      · decide +kernel
def slice136 : Slice := ⟨cover136,(8/7),(4/3),(241867005/2147483648)⟩
theorem slice136_checked : accepts 1 0 4 slice136=true :=
  accepts_of_checks 1 0 4 slice136 (by decide +kernel) (by decide +kernel) cover136_checked
def cover137 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00411) (.second (3/4) (.leaf leaf00412) (.leaf leaf00413)))
theorem cover137_checked : FastArmCover.accepts 1 0 4 (4/3) (8/5) 0 1 0 1 (120082391/1073741824) cover137=true := by
  unfold cover137
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00411_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00412_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00413_checked
      · decide +kernel
      · decide +kernel
def slice137 : Slice := ⟨cover137,(4/3),(8/5),(120082391/1073741824)⟩
theorem slice137_checked : accepts 1 0 4 slice137=true :=
  accepts_of_checks 1 0 4 slice137 (by decide +kernel) (by decide +kernel) cover137_checked
def cover138 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00414) (.second (3/4) (.leaf leaf00415) (.leaf leaf00416)))
theorem cover138_checked : FastArmCover.accepts 1 0 4 (8/5) (16/9) 0 1 0 1 (57565233/536870912) cover138=true := by
  unfold cover138
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00414_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00415_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00416_checked
      · decide +kernel
      · decide +kernel
def slice138 : Slice := ⟨cover138,(8/5),(16/9),(57565233/536870912)⟩
theorem slice138_checked : accepts 1 0 4 slice138=true :=
  accepts_of_checks 1 0 4 slice138 (by decide +kernel) (by decide +kernel) cover138_checked
def cover139 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00417) (.second (3/4) (.leaf leaf00418) (.leaf leaf00419)))
theorem cover139_checked : FastArmCover.accepts 1 0 4 (16/9) 2 0 1 0 1 (213638135/2147483648) cover139=true := by
  unfold cover139
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00417_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00418_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00419_checked
      · decide +kernel
      · decide +kernel
def slice139 : Slice := ⟨cover139,(16/9),2,(213638135/2147483648)⟩
theorem slice139_checked : accepts 1 0 4 slice139=true :=
  accepts_of_checks 1 0 4 slice139 (by decide +kernel) (by decide +kernel) cover139_checked
def cover140 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00420) (.second (3/4) (.leaf leaf00421) (.leaf leaf00422)))
theorem cover140_checked : FastArmCover.accepts 1 0 4 2 (16/7) 0 1 0 1 (382708623/4294967296) cover140=true := by
  unfold cover140
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00420_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00421_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00422_checked
      · decide +kernel
      · decide +kernel
def slice140 : Slice := ⟨cover140,2,(16/7),(382708623/4294967296)⟩
theorem slice140_checked : accepts 1 0 4 slice140=true :=
  accepts_of_checks 1 0 4 slice140 (by decide +kernel) (by decide +kernel) cover140_checked
def cover141 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00423) (.second (3/4) (.leaf leaf00424) (.leaf leaf00425)))
theorem cover141_checked : FastArmCover.accepts 1 0 4 (16/7) (32/13) 0 1 0 1 (178622563/2147483648) cover141=true := by
  unfold cover141
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00423_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00424_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00425_checked
      · decide +kernel
      · decide +kernel
def slice141 : Slice := ⟨cover141,(16/7),(32/13),(178622563/2147483648)⟩
theorem slice141_checked : accepts 1 0 4 slice141=true :=
  accepts_of_checks 1 0 4 slice141 (by decide +kernel) (by decide +kernel) cover141_checked
def cover142 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00426) (.second (3/4) (.leaf leaf00427) (.leaf leaf00428)))
theorem cover142_checked : FastArmCover.accepts 1 0 4 (32/13) (8/3) 0 1 0 1 (328143831/4294967296) cover142=true := by
  unfold cover142
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00426_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00427_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00428_checked
      · decide +kernel
      · decide +kernel
def slice142 : Slice := ⟨cover142,(32/13),(8/3),(328143831/4294967296)⟩
theorem slice142_checked : accepts 1 0 4 slice142=true :=
  accepts_of_checks 1 0 4 slice142 (by decide +kernel) (by decide +kernel) cover142_checked
def cover143 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00429) (.second (3/4) (.leaf leaf00430) (.leaf leaf00431)))
theorem cover143_checked : FastArmCover.accepts 1 0 4 (8/3) (32/11) 0 1 0 1 (37080497/536870912) cover143=true := by
  unfold cover143
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00429_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00430_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00431_checked
      · decide +kernel
      · decide +kernel
def slice143 : Slice := ⟨cover143,(8/3),(32/11),(37080497/536870912)⟩
theorem slice143_checked : accepts 1 0 4 slice143=true :=
  accepts_of_checks 1 0 4 slice143 (by decide +kernel) (by decide +kernel) cover143_checked
def cover144 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00432) (.second (3/4) (.leaf leaf00433) (.leaf leaf00434)))
theorem cover144_checked : FastArmCover.accepts 1 0 4 (32/11) (16/5) 0 1 0 1 (263116759/4294967296) cover144=true := by
  unfold cover144
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00432_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00433_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00434_checked
      · decide +kernel
      · decide +kernel
def slice144 : Slice := ⟨cover144,(32/11),(16/5),(263116759/4294967296)⟩
theorem slice144_checked : accepts 1 0 4 slice144=true :=
  accepts_of_checks 1 0 4 slice144 (by decide +kernel) (by decide +kernel) cover144_checked
def cover145 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00435) (.second (3/4) (.leaf leaf00436) (.leaf leaf00437)))
theorem cover145_checked : FastArmCover.accepts 1 0 4 (16/5) (32/9) 0 1 0 1 (228077245/4294967296) cover145=true := by
  unfold cover145
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00435_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00436_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00437_checked
      · decide +kernel
      · decide +kernel
def slice145 : Slice := ⟨cover145,(16/5),(32/9),(228077245/4294967296)⟩
theorem slice145_checked : accepts 1 0 4 slice145=true :=
  accepts_of_checks 1 0 4 slice145 (by decide +kernel) (by decide +kernel) cover145_checked
def cover146 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00438) (.second (3/4) (.leaf leaf00439) (.leaf leaf00440)))
theorem cover146_checked : FastArmCover.accepts 1 0 4 (32/9) (64/17) 0 1 0 1 (210473121/4294967296) cover146=true := by
  unfold cover146
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00438_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00439_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00440_checked
      · decide +kernel
      · decide +kernel
def slice146 : Slice := ⟨cover146,(32/9),(64/17),(210473121/4294967296)⟩
theorem slice146_checked : accepts 1 0 4 slice146=true :=
  accepts_of_checks 1 0 4 slice146 (by decide +kernel) (by decide +kernel) cover146_checked
def cover147 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00441) (.second (3/4) (.leaf leaf00442) (.leaf leaf00443)))
theorem cover147_checked : FastArmCover.accepts 1 0 4 (64/17) 4 0 1 0 1 (96236663/2147483648) cover147=true := by
  unfold cover147
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00441_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00442_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00443_checked
      · decide +kernel
      · decide +kernel
def slice147 : Slice := ⟨cover147,(64/17),4,(96236663/2147483648)⟩
theorem slice147_checked : accepts 1 0 4 slice147=true :=
  accepts_of_checks 1 0 4 slice147 (by decide +kernel) (by decide +kernel) cover147_checked
def cover148 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00444) (.second (3/4) (.leaf leaf00445) (.leaf leaf00446)))
theorem cover148_checked : FastArmCover.accepts 1 0 4 4 (64/15) 0 1 0 1 (174470249/4294967296) cover148=true := by
  unfold cover148
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00444_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00445_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00446_checked
      · decide +kernel
      · decide +kernel
def slice148 : Slice := ⟨cover148,4,(64/15),(174470249/4294967296)⟩
theorem slice148_checked : accepts 1 0 4 slice148=true :=
  accepts_of_checks 1 0 4 slice148 (by decide +kernel) (by decide +kernel) cover148_checked
def cover149 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00447) (.second (3/4) (.leaf leaf00448) (.leaf leaf00449)))
theorem cover149_checked : FastArmCover.accepts 1 0 4 (64/15) (32/7) 0 1 0 1 (156584457/4294967296) cover149=true := by
  unfold cover149
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00447_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00448_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00449_checked
      · decide +kernel
      · decide +kernel
def slice149 : Slice := ⟨cover149,(64/15),(32/7),(156584457/4294967296)⟩
theorem slice149_checked : accepts 1 0 4 slice149=true :=
  accepts_of_checks 1 0 4 slice149 (by decide +kernel) (by decide +kernel) cover149_checked
def cover150 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00450) (.second (3/4) (.leaf leaf00451) (.leaf leaf00452)))
theorem cover150_checked : FastArmCover.accepts 1 0 4 (32/7) (64/13) 0 1 0 1 (69473115/2147483648) cover150=true := by
  unfold cover150
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00450_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00451_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00452_checked
      · decide +kernel
      · decide +kernel
def slice150 : Slice := ⟨cover150,(32/7),(64/13),(69473115/2147483648)⟩
theorem slice150_checked : accepts 1 0 4 slice150=true :=
  accepts_of_checks 1 0 4 slice150 (by decide +kernel) (by decide +kernel) cover150_checked
def cover151 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00453) (.second (3/4) (.leaf leaf00454) (.leaf leaf00455)))
theorem cover151_checked : FastArmCover.accepts 1 0 4 (64/13) (16/3) 0 1 0 1 (237685/8388608) cover151=true := by
  unfold cover151
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00453_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00454_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00455_checked
      · decide +kernel
      · decide +kernel
def slice151 : Slice := ⟨cover151,(64/13),(16/3),(237685/8388608)⟩
theorem slice151_checked : accepts 1 0 4 slice151=true :=
  accepts_of_checks 1 0 4 slice151 (by decide +kernel) (by decide +kernel) cover151_checked
def cover152 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00456) (.second (3/4) (.leaf leaf00457) (.leaf leaf00458)))
theorem cover152_checked : FastArmCover.accepts 1 0 4 (16/3) (64/11) 0 1 0 1 (52488397/2147483648) cover152=true := by
  unfold cover152
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00456_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00457_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00458_checked
      · decide +kernel
      · decide +kernel
def slice152 : Slice := ⟨cover152,(16/3),(64/11),(52488397/2147483648)⟩
theorem slice152_checked : accepts 1 0 4 slice152=true :=
  accepts_of_checks 1 0 4 slice152 (by decide +kernel) (by decide +kernel) cover152_checked
def cover153 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00459) (.second (3/4) (.leaf leaf00460) (.leaf leaf00461)))
theorem cover153_checked : FastArmCover.accepts 1 0 4 (64/11) (32/5) 0 1 0 1 (88945517/4294967296) cover153=true := by
  unfold cover153
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00459_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00460_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00461_checked
      · decide +kernel
      · decide +kernel
def slice153 : Slice := ⟨cover153,(64/11),(32/5),(88945517/4294967296)⟩
theorem slice153_checked : accepts 1 0 4 slice153=true :=
  accepts_of_checks 1 0 4 slice153 (by decide +kernel) (by decide +kernel) cover153_checked
def cover154 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00462) (.second (3/4) (.leaf leaf00463) (.leaf leaf00464)))
theorem cover154_checked : FastArmCover.accepts 1 0 4 (32/5) (64/9) 0 1 0 1 (9219789/536870912) cover154=true := by
  unfold cover154
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00462_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00463_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00464_checked
      · decide +kernel
      · decide +kernel
def slice154 : Slice := ⟨cover154,(32/5),(64/9),(9219789/536870912)⟩
theorem slice154_checked : accepts 1 0 4 slice154=true :=
  accepts_of_checks 1 0 4 slice154 (by decide +kernel) (by decide +kernel) cover154_checked
def cover155 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00465) (.second (3/4) (.leaf leaf00466) (.leaf leaf00467)))
theorem cover155_checked : FastArmCover.accepts 1 0 4 (64/9) 8 0 1 0 1 (29787385/2147483648) cover155=true := by
  unfold cover155
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00465_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00466_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00467_checked
      · decide +kernel
      · decide +kernel
def slice155 : Slice := ⟨cover155,(64/9),8,(29787385/2147483648)⟩
theorem slice155_checked : accepts 1 0 4 slice155=true :=
  accepts_of_checks 1 0 4 slice155 (by decide +kernel) (by decide +kernel) cover155_checked
def cover156 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00468) (.second (3/4) (.leaf leaf00469) (.leaf leaf00470)))
theorem cover156_checked : FastArmCover.accepts 1 0 4 8 (64/7) 0 1 0 1 (23277093/2147483648) cover156=true := by
  unfold cover156
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00468_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00469_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00470_checked
      · decide +kernel
      · decide +kernel
def slice156 : Slice := ⟨cover156,8,(64/7),(23277093/2147483648)⟩
theorem slice156_checked : accepts 1 0 4 slice156=true :=
  accepts_of_checks 1 0 4 slice156 (by decide +kernel) (by decide +kernel) cover156_checked
def cover157 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00471) (.second (3/4) (.leaf leaf00472) (.leaf leaf00473)))
theorem cover157_checked : FastArmCover.accepts 1 0 4 (64/7) (128/13) 0 1 0 1 (40567429/4294967296) cover157=true := by
  unfold cover157
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00471_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00472_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00473_checked
      · decide +kernel
      · decide +kernel
def slice157 : Slice := ⟨cover157,(64/7),(128/13),(40567429/4294967296)⟩
theorem slice157_checked : accepts 1 0 4 slice157=true :=
  accepts_of_checks 1 0 4 slice157 (by decide +kernel) (by decide +kernel) cover157_checked
def cover158 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00474) (.second (3/4) (.leaf leaf00475) (.leaf leaf00476)))
theorem cover158_checked : FastArmCover.accepts 1 0 4 (128/13) (32/3) 0 1 0 1 (34888451/4294967296) cover158=true := by
  unfold cover158
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00474_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00475_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00476_checked
      · decide +kernel
      · decide +kernel
def slice158 : Slice := ⟨cover158,(128/13),(32/3),(34888451/4294967296)⟩
theorem slice158_checked : accepts 1 0 4 slice158=true :=
  accepts_of_checks 1 0 4 slice158 (by decide +kernel) (by decide +kernel) cover158_checked
def cover159 : FastArmCover.Cover := (.second (1/2) (.second (1/4) (.leaf leaf00477) (.leaf leaf00478)) (.leaf leaf00479))
theorem cover159_checked : FastArmCover.accepts 1 0 4 (32/3) (128/11) 0 1 0 1 (29576945/4294967296) cover159=true := by
  unfold cover159
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00477_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00478_checked
      · decide +kernel
      · decide +kernel
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00479_checked
    · decide +kernel
    · decide +kernel
def slice159 : Slice := ⟨cover159,(32/3),(128/11),(29576945/4294967296)⟩
theorem slice159_checked : accepts 1 0 4 slice159=true :=
  accepts_of_checks 1 0 4 slice159 (by decide +kernel) (by decide +kernel) cover159_checked
def cover160 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00480) (.second (3/4) (.leaf leaf00481) (.leaf leaf00482)))
theorem cover160_checked : FastArmCover.accepts 1 0 4 (128/11) (64/5) 0 1 0 1 (24650967/4294967296) cover160=true := by
  unfold cover160
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00480_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00481_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00482_checked
      · decide +kernel
      · decide +kernel
def slice160 : Slice := ⟨cover160,(128/11),(64/5),(24650967/4294967296)⟩
theorem slice160_checked : accepts 1 0 4 slice160=true :=
  accepts_of_checks 1 0 4 slice160 (by decide +kernel) (by decide +kernel) cover160_checked
def cover161 : FastArmCover.Cover := (.second (1/2) (.leaf leaf00483) (.second (3/4) (.leaf leaf00484) (.leaf leaf00485)))
theorem cover161_checked : FastArmCover.accepts 1 0 4 (64/5) (128/9) 0 1 0 1 (5031983/1073741824) cover161=true := by
  unfold cover161
  apply FastArmCover.second_of_checks
  ·
    apply FastArmCover.leaf_of_checks
    · exact leaf00483_checked
    · decide +kernel
    · decide +kernel
  ·
    apply FastArmCover.second_of_checks
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00484_checked
      · decide +kernel
      · decide +kernel
    ·
      apply FastArmCover.leaf_of_checks
      · exact leaf00485_checked
      · decide +kernel
      · decide +kernel
def slice161 : Slice := ⟨cover161,(64/5),(128/9),(5031983/1073741824)⟩
theorem slice161_checked : accepts 1 0 4 slice161=true :=
  accepts_of_checks 1 0 4 slice161 (by decide +kernel) (by decide +kernel) cover161_checked
def cover162 : FastArmCover.Cover := (.leaf leaf00486)
theorem cover162_checked : FastArmCover.accepts 1 0 4 (128/9) 16 0 1 0 1 (16024525/4294967296) cover162=true := by
  unfold cover162
  apply FastArmCover.leaf_of_checks
  · exact leaf00486_checked
  · decide +kernel
  · decide +kernel
def slice162 : Slice := ⟨cover162,(128/9),16,(16024525/4294967296)⟩
theorem slice162_checked : accepts 1 0 4 slice162=true :=
  accepts_of_checks 1 0 4 slice162 (by decide +kernel) (by decide +kernel) cover162_checked
def cover163 : FastArmCover.Cover := (.leaf leaf00487)
theorem cover163_checked : FastArmCover.accepts 1 0 4 16 (128/7) 0 1 0 1 (6178307/2147483648) cover163=true := by
  unfold cover163
  apply FastArmCover.leaf_of_checks
  · exact leaf00487_checked
  · decide +kernel
  · decide +kernel
def slice163 : Slice := ⟨cover163,16,(128/7),(6178307/2147483648)⟩
theorem slice163_checked : accepts 1 0 4 slice163=true :=
  accepts_of_checks 1 0 4 slice163 (by decide +kernel) (by decide +kernel) cover163_checked
def cover164 : FastArmCover.Cover := (.leaf leaf00488)
theorem cover164_checked : FastArmCover.accepts 1 0 4 (128/7) (64/3) 0 1 0 1 (285599/134217728) cover164=true := by
  unfold cover164
  apply FastArmCover.leaf_of_checks
  · exact leaf00488_checked
  · decide +kernel
  · decide +kernel
def slice164 : Slice := ⟨cover164,(128/7),(64/3),(285599/134217728)⟩
theorem slice164_checked : accepts 1 0 4 slice164=true :=
  accepts_of_checks 1 0 4 slice164 (by decide +kernel) (by decide +kernel) cover164_checked
def cover165 : FastArmCover.Cover := (.leaf leaf00489)
theorem cover165_checked : FastArmCover.accepts 1 0 4 (64/3) (128/5) 0 1 0 1 (12473/8388608) cover165=true := by
  unfold cover165
  apply FastArmCover.leaf_of_checks
  · exact leaf00489_checked
  · decide +kernel
  · decide +kernel
def slice165 : Slice := ⟨cover165,(64/3),(128/5),(12473/8388608)⟩
theorem slice165_checked : accepts 1 0 4 slice165=true :=
  accepts_of_checks 1 0 4 slice165 (by decide +kernel) (by decide +kernel) cover165_checked
def cover166 : FastArmCover.Cover := (.leaf leaf00490)
theorem cover166_checked : FastArmCover.accepts 1 0 4 (128/5) 32 0 1 0 1 (1027643/1073741824) cover166=true := by
  unfold cover166
  apply FastArmCover.leaf_of_checks
  · exact leaf00490_checked
  · decide +kernel
  · decide +kernel
def slice166 : Slice := ⟨cover166,(128/5),32,(1027643/1073741824)⟩
theorem slice166_checked : accepts 1 0 4 slice166=true :=
  accepts_of_checks 1 0 4 slice166 (by decide +kernel) (by decide +kernel) cover166_checked
def cover167 : FastArmCover.Cover := (.leaf leaf00491)
theorem cover167_checked : FastArmCover.accepts 1 0 4 32 (256/7) 0 1 0 1 (3158139/4294967296) cover167=true := by
  unfold cover167
  apply FastArmCover.leaf_of_checks
  · exact leaf00491_checked
  · decide +kernel
  · decide +kernel
def slice167 : Slice := ⟨cover167,32,(256/7),(3158139/4294967296)⟩
theorem slice167_checked : accepts 1 0 4 slice167=true :=
  accepts_of_checks 1 0 4 slice167 (by decide +kernel) (by decide +kernel) cover167_checked
def cover168 : FastArmCover.Cover := (.leaf leaf00492)
theorem cover168_checked : FastArmCover.accepts 1 0 4 (256/7) (128/3) 0 1 0 1 (72699/134217728) cover168=true := by
  unfold cover168
  apply FastArmCover.leaf_of_checks
  · exact leaf00492_checked
  · decide +kernel
  · decide +kernel
def slice168 : Slice := ⟨cover168,(256/7),(128/3),(72699/134217728)⟩
theorem slice168_checked : accepts 1 0 4 slice168=true :=
  accepts_of_checks 1 0 4 slice168 (by decide +kernel) (by decide +kernel) cover168_checked
def cover169 : FastArmCover.Cover := (.leaf leaf00493)
theorem cover169_checked : FastArmCover.accepts 1 0 4 (128/3) (256/5) 0 1 0 1 (1619577/4294967296) cover169=true := by
  unfold cover169
  apply FastArmCover.leaf_of_checks
  · exact leaf00493_checked
  · decide +kernel
  · decide +kernel
def slice169 : Slice := ⟨cover169,(128/3),(256/5),(1619577/4294967296)⟩
theorem slice169_checked : accepts 1 0 4 slice169=true :=
  accepts_of_checks 1 0 4 slice169 (by decide +kernel) (by decide +kernel) cover169_checked
def cover170 : FastArmCover.Cover := (.leaf leaf00494)
theorem cover170_checked : FastArmCover.accepts 1 0 4 (256/5) 64 0 1 0 1 (519489/2147483648) cover170=true := by
  unfold cover170
  apply FastArmCover.leaf_of_checks
  · exact leaf00494_checked
  · decide +kernel
  · decide +kernel
def slice170 : Slice := ⟨cover170,(256/5),64,(519489/2147483648)⟩
theorem slice170_checked : accepts 1 0 4 slice170=true :=
  accepts_of_checks 1 0 4 slice170 (by decide +kernel) (by decide +kernel) cover170_checked
def cover171 : FastArmCover.Cover := (.leaf leaf00495)
theorem cover171_checked : FastArmCover.accepts 1 0 4 64 (256/3) 0 1 0 1 (292855/2147483648) cover171=true := by
  unfold cover171
  apply FastArmCover.leaf_of_checks
  · exact leaf00495_checked
  · decide +kernel
  · decide +kernel
def slice171 : Slice := ⟨cover171,64,(256/3),(292855/2147483648)⟩
theorem slice171_checked : accepts 1 0 4 slice171=true :=
  accepts_of_checks 1 0 4 slice171 (by decide +kernel) (by decide +kernel) cover171_checked
def cover172 : FastArmCover.Cover := (.leaf leaf00496)
theorem cover172_checked : FastArmCover.accepts 1 0 4 (256/3) 128 0 1 0 1 (130413/2147483648) cover172=true := by
  unfold cover172
  apply FastArmCover.leaf_of_checks
  · exact leaf00496_checked
  · decide +kernel
  · decide +kernel
def slice172 : Slice := ⟨cover172,(256/3),128,(130413/2147483648)⟩
theorem slice172_checked : accepts 1 0 4 slice172=true :=
  accepts_of_checks 1 0 4 slice172 (by decide +kernel) (by decide +kernel) cover172_checked
def cover173 : FastArmCover.Cover := (.leaf leaf00497)
theorem cover173_checked : FastArmCover.accepts 1 0 4 128 (512/3) 0 1 0 1 (73479/2147483648) cover173=true := by
  unfold cover173
  apply FastArmCover.leaf_of_checks
  · exact leaf00497_checked
  · decide +kernel
  · decide +kernel
def slice173 : Slice := ⟨cover173,128,(512/3),(73479/2147483648)⟩
theorem slice173_checked : accepts 1 0 4 slice173=true :=
  accepts_of_checks 1 0 4 slice173 (by decide +kernel) (by decide +kernel) cover173_checked
def cover174 : FastArmCover.Cover := (.leaf leaf00498)
theorem cover174_checked : FastArmCover.accepts 1 0 4 (512/3) 256 0 1 0 1 (32687/2147483648) cover174=true := by
  unfold cover174
  apply FastArmCover.leaf_of_checks
  · exact leaf00498_checked
  · decide +kernel
  · decide +kernel
def slice174 : Slice := ⟨cover174,(512/3),256,(32687/2147483648)⟩
theorem slice174_checked : accepts 1 0 4 slice174=true :=
  accepts_of_checks 1 0 4 slice174 (by decide +kernel) (by decide +kernel) cover174_checked
def cover175 : FastArmCover.Cover := (.leaf leaf00499)
theorem cover175_checked : FastArmCover.accepts 1 0 4 256 512 0 1 0 1 (16353/4294967296) cover175=true := by
  unfold cover175
  apply FastArmCover.leaf_of_checks
  · exact leaf00499_checked
  · decide +kernel
  · decide +kernel
def slice175 : Slice := ⟨cover175,256,512,(16353/4294967296)⟩
theorem slice175_checked : accepts 1 0 4 slice175=true :=
  accepts_of_checks 1 0 4 slice175 (by decide +kernel) (by decide +kernel) cover175_checked
def cover176 : FastArmCover.Cover := (.leaf leaf00500)
theorem cover176_checked : FastArmCover.accepts 1 0 4 512 1024 0 1 0 1 (4091/4294967296) cover176=true := by
  unfold cover176
  apply FastArmCover.leaf_of_checks
  · exact leaf00500_checked
  · decide +kernel
  · decide +kernel
def slice176 : Slice := ⟨cover176,512,1024,(4091/4294967296)⟩
theorem slice176_checked : accepts 1 0 4 slice176=true :=
  accepts_of_checks 1 0 4 slice176 (by decide +kernel) (by decide +kernel) cover176_checked
def partition : List Slice := [slice000,slice001,slice002,slice003,slice004,slice005,slice006,slice007,slice008,slice009,slice010,slice011,slice012,slice013,slice014,slice015,slice016,slice017,slice018,slice019,slice020,slice021,slice022,slice023,slice024,slice025,slice026,slice027,slice028,slice029,slice030,slice031,slice032,slice033,slice034,slice035,slice036,slice037,slice038,slice039,slice040,slice041,slice042,slice043,slice044,slice045,slice046,slice047,slice048,slice049,slice050,slice051,slice052,slice053,slice054,slice055,slice056,slice057,slice058,slice059,slice060,slice061,slice062,slice063,slice064,slice065,slice066,slice067,slice068,slice069,slice070,slice071,slice072,slice073,slice074,slice075,slice076,slice077,slice078,slice079,slice080,slice081,slice082,slice083,slice084,slice085,slice086,slice087,slice088,slice089,slice090,slice091,slice092,slice093,slice094,slice095,slice096,slice097,slice098,slice099,slice100,slice101,slice102,slice103,slice104,slice105,slice106,slice107,slice108,slice109,slice110,slice111,slice112,slice113,slice114,slice115,slice116,slice117,slice118,slice119,slice120,slice121,slice122,slice123,slice124,slice125,slice126,slice127,slice128,slice129,slice130,slice131,slice132,slice133,slice134,slice135,slice136,slice137,slice138,slice139,slice140,slice141,slice142,slice143,slice144,slice145,slice146,slice147,slice148,slice149,slice150,slice151,slice152,slice153,slice154,slice155,slice156,slice157,slice158,slice159,slice160,slice161,slice162,slice163,slice164,slice165,slice166,slice167,slice168,slice169,slice170,slice171,slice172,slice173,slice174,slice175,slice176]
theorem partition_checked : checkAt 1 0 4 (1/1000) 1024 partition=true := by
  unfold partition
  apply checked_cons _ _ _ _ _ _ _ rfl slice000_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice001_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice002_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice003_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice004_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice005_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice006_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice007_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice008_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice009_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice010_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice011_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice012_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice013_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice014_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice015_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice016_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice017_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice018_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice019_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice020_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice021_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice022_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice023_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice024_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice025_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice026_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice027_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice028_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice029_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice030_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice031_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice032_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice033_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice034_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice035_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice036_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice037_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice038_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice039_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice040_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice041_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice042_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice043_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice044_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice045_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice046_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice047_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice048_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice049_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice050_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice051_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice052_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice053_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice054_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice055_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice056_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice057_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice058_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice059_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice060_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice061_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice062_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice063_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice064_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice065_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice066_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice067_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice068_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice069_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice070_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice071_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice072_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice073_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice074_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice075_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice076_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice077_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice078_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice079_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice080_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice081_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice082_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice083_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice084_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice085_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice086_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice087_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice088_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice089_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice090_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice091_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice092_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice093_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice094_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice095_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice096_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice097_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice098_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice099_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice100_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice101_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice102_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice103_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice104_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice105_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice106_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice107_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice108_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice109_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice110_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice111_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice112_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice113_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice114_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice115_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice116_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice117_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice118_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice119_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice120_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice121_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice122_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice123_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice124_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice125_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice126_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice127_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice128_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice129_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice130_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice131_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice132_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice133_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice134_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice135_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice136_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice137_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice138_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice139_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice140_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice141_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice142_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice143_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice144_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice145_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice146_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice147_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice148_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice149_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice150_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice151_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice152_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice153_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice154_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice155_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice156_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice157_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice158_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice159_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice160_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice161_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice162_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice163_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice164_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice165_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice166_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice167_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice168_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice169_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice170_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice171_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice172_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice173_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice174_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice175_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice176_checked
  decide +kernel
theorem budget_checked : FastPaidDegreeOneClass.accepts (payment partition)=true := by decide +kernel
noncomputable section
open scoped Classical
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=0) (hq : ArmClasses.classify q=4) :
    (189/5000 : ℝ) < ActualFusionIntegral.normalizedIntegral C u p q 2 :=
  FastArmCoverIntegral.normalized_target C u p q hd 0 4 hp hq partition partition_checked budget_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
