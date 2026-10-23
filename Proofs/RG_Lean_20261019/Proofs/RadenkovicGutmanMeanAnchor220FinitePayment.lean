/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch000
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch001
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch002
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch003
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch004
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch005
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch006
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch007
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch008
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch009
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch010
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch011
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch012
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch013
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch014
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch015
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch016
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch017
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch018
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch019
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch020
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch021
import Proofs.RadenkovicGutmanMeanAnchor220FastBatch022
import Proofs.RadenkovicGutmanRationalIntegralPartition

namespace Gebendorfer.RadenkovicGutman.MeanAnchor220FinitePayment
open Set MeasureTheory RationalIntegralPartition
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def slices : List Slice := [
  ⟨MeanAnchor220FastPolynomialCell000.cell.a,MeanAnchor220FastPolynomialCell000.cell.b,MeanAnchor220FastPolynomialCell000.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell001.cell.a,MeanAnchor220FastPolynomialCell001.cell.b,MeanAnchor220FastPolynomialCell001.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell002.cell.a,MeanAnchor220FastPolynomialCell002.cell.b,MeanAnchor220FastPolynomialCell002.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell003.cell.a,MeanAnchor220FastPolynomialCell003.cell.b,MeanAnchor220FastPolynomialCell003.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell004.cell.a,MeanAnchor220FastPolynomialCell004.cell.b,MeanAnchor220FastPolynomialCell004.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell005.cell.a,MeanAnchor220FastPolynomialCell005.cell.b,MeanAnchor220FastPolynomialCell005.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell006.cell.a,MeanAnchor220FastPolynomialCell006.cell.b,MeanAnchor220FastPolynomialCell006.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell007.cell.a,MeanAnchor220FastPolynomialCell007.cell.b,MeanAnchor220FastPolynomialCell007.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell008.cell.a,MeanAnchor220FastPolynomialCell008.cell.b,MeanAnchor220FastPolynomialCell008.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell009.cell.a,MeanAnchor220FastPolynomialCell009.cell.b,MeanAnchor220FastPolynomialCell009.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell010.cell.a,MeanAnchor220FastPolynomialCell010.cell.b,MeanAnchor220FastPolynomialCell010.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell011.cell.a,MeanAnchor220FastPolynomialCell011.cell.b,MeanAnchor220FastPolynomialCell011.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell012.cell.a,MeanAnchor220FastPolynomialCell012.cell.b,MeanAnchor220FastPolynomialCell012.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell013.cell.a,MeanAnchor220FastPolynomialCell013.cell.b,MeanAnchor220FastPolynomialCell013.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell014.cell.a,MeanAnchor220FastPolynomialCell014.cell.b,MeanAnchor220FastPolynomialCell014.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell015.cell.a,MeanAnchor220FastPolynomialCell015.cell.b,MeanAnchor220FastPolynomialCell015.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell016.cell.a,MeanAnchor220FastPolynomialCell016.cell.b,MeanAnchor220FastPolynomialCell016.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell017.cell.a,MeanAnchor220FastPolynomialCell017.cell.b,MeanAnchor220FastPolynomialCell017.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell018.cell.a,MeanAnchor220FastPolynomialCell018.cell.b,MeanAnchor220FastPolynomialCell018.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell019.cell.a,MeanAnchor220FastPolynomialCell019.cell.b,MeanAnchor220FastPolynomialCell019.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell020.cell.a,MeanAnchor220FastPolynomialCell020.cell.b,MeanAnchor220FastPolynomialCell020.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell021.cell.a,MeanAnchor220FastPolynomialCell021.cell.b,MeanAnchor220FastPolynomialCell021.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell022.cell.a,MeanAnchor220FastPolynomialCell022.cell.b,MeanAnchor220FastPolynomialCell022.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell023.cell.a,MeanAnchor220FastPolynomialCell023.cell.b,MeanAnchor220FastPolynomialCell023.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell024.cell.a,MeanAnchor220FastPolynomialCell024.cell.b,MeanAnchor220FastPolynomialCell024.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell025.cell.a,MeanAnchor220FastPolynomialCell025.cell.b,MeanAnchor220FastPolynomialCell025.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell026.cell.a,MeanAnchor220FastPolynomialCell026.cell.b,MeanAnchor220FastPolynomialCell026.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell027.cell.a,MeanAnchor220FastPolynomialCell027.cell.b,MeanAnchor220FastPolynomialCell027.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell028.cell.a,MeanAnchor220FastPolynomialCell028.cell.b,MeanAnchor220FastPolynomialCell028.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell029.cell.a,MeanAnchor220FastPolynomialCell029.cell.b,MeanAnchor220FastPolynomialCell029.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell030.cell.a,MeanAnchor220FastPolynomialCell030.cell.b,MeanAnchor220FastPolynomialCell030.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell031.cell.a,MeanAnchor220FastPolynomialCell031.cell.b,MeanAnchor220FastPolynomialCell031.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell032.cell.a,MeanAnchor220FastPolynomialCell032.cell.b,MeanAnchor220FastPolynomialCell032.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell033.cell.a,MeanAnchor220FastPolynomialCell033.cell.b,MeanAnchor220FastPolynomialCell033.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell034.cell.a,MeanAnchor220FastPolynomialCell034.cell.b,MeanAnchor220FastPolynomialCell034.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell035.cell.a,MeanAnchor220FastPolynomialCell035.cell.b,MeanAnchor220FastPolynomialCell035.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell036.cell.a,MeanAnchor220FastPolynomialCell036.cell.b,MeanAnchor220FastPolynomialCell036.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell037.cell.a,MeanAnchor220FastPolynomialCell037.cell.b,MeanAnchor220FastPolynomialCell037.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell038.cell.a,MeanAnchor220FastPolynomialCell038.cell.b,MeanAnchor220FastPolynomialCell038.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell039.cell.a,MeanAnchor220FastPolynomialCell039.cell.b,MeanAnchor220FastPolynomialCell039.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell040.cell.a,MeanAnchor220FastPolynomialCell040.cell.b,MeanAnchor220FastPolynomialCell040.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell041.cell.a,MeanAnchor220FastPolynomialCell041.cell.b,MeanAnchor220FastPolynomialCell041.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell042.cell.a,MeanAnchor220FastPolynomialCell042.cell.b,MeanAnchor220FastPolynomialCell042.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell043.cell.a,MeanAnchor220FastPolynomialCell043.cell.b,MeanAnchor220FastPolynomialCell043.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell044.cell.a,MeanAnchor220FastPolynomialCell044.cell.b,MeanAnchor220FastPolynomialCell044.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell045.cell.a,MeanAnchor220FastPolynomialCell045.cell.b,MeanAnchor220FastPolynomialCell045.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell046.cell.a,MeanAnchor220FastPolynomialCell046.cell.b,MeanAnchor220FastPolynomialCell046.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell047.cell.a,MeanAnchor220FastPolynomialCell047.cell.b,MeanAnchor220FastPolynomialCell047.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell048.cell.a,MeanAnchor220FastPolynomialCell048.cell.b,MeanAnchor220FastPolynomialCell048.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell049.cell.a,MeanAnchor220FastPolynomialCell049.cell.b,MeanAnchor220FastPolynomialCell049.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell050.cell.a,MeanAnchor220FastPolynomialCell050.cell.b,MeanAnchor220FastPolynomialCell050.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell051.cell.a,MeanAnchor220FastPolynomialCell051.cell.b,MeanAnchor220FastPolynomialCell051.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell052.cell.a,MeanAnchor220FastPolynomialCell052.cell.b,MeanAnchor220FastPolynomialCell052.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell053.cell.a,MeanAnchor220FastPolynomialCell053.cell.b,MeanAnchor220FastPolynomialCell053.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell054.cell.a,MeanAnchor220FastPolynomialCell054.cell.b,MeanAnchor220FastPolynomialCell054.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell055.cell.a,MeanAnchor220FastPolynomialCell055.cell.b,MeanAnchor220FastPolynomialCell055.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell056.cell.a,MeanAnchor220FastPolynomialCell056.cell.b,MeanAnchor220FastPolynomialCell056.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell057.cell.a,MeanAnchor220FastPolynomialCell057.cell.b,MeanAnchor220FastPolynomialCell057.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell058.cell.a,MeanAnchor220FastPolynomialCell058.cell.b,MeanAnchor220FastPolynomialCell058.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell059.cell.a,MeanAnchor220FastPolynomialCell059.cell.b,MeanAnchor220FastPolynomialCell059.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell060.cell.a,MeanAnchor220FastPolynomialCell060.cell.b,MeanAnchor220FastPolynomialCell060.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell061.cell.a,MeanAnchor220FastPolynomialCell061.cell.b,MeanAnchor220FastPolynomialCell061.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell062.cell.a,MeanAnchor220FastPolynomialCell062.cell.b,MeanAnchor220FastPolynomialCell062.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell063.cell.a,MeanAnchor220FastPolynomialCell063.cell.b,MeanAnchor220FastPolynomialCell063.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell064.cell.a,MeanAnchor220FastPolynomialCell064.cell.b,MeanAnchor220FastPolynomialCell064.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell065.cell.a,MeanAnchor220FastPolynomialCell065.cell.b,MeanAnchor220FastPolynomialCell065.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell066.cell.a,MeanAnchor220FastPolynomialCell066.cell.b,MeanAnchor220FastPolynomialCell066.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell067.cell.a,MeanAnchor220FastPolynomialCell067.cell.b,MeanAnchor220FastPolynomialCell067.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell068.cell.a,MeanAnchor220FastPolynomialCell068.cell.b,MeanAnchor220FastPolynomialCell068.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell069.cell.a,MeanAnchor220FastPolynomialCell069.cell.b,MeanAnchor220FastPolynomialCell069.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell070.cell.a,MeanAnchor220FastPolynomialCell070.cell.b,MeanAnchor220FastPolynomialCell070.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell071.cell.a,MeanAnchor220FastPolynomialCell071.cell.b,MeanAnchor220FastPolynomialCell071.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell072.cell.a,MeanAnchor220FastPolynomialCell072.cell.b,MeanAnchor220FastPolynomialCell072.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell073.cell.a,MeanAnchor220FastPolynomialCell073.cell.b,MeanAnchor220FastPolynomialCell073.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell074.cell.a,MeanAnchor220FastPolynomialCell074.cell.b,MeanAnchor220FastPolynomialCell074.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell075.cell.a,MeanAnchor220FastPolynomialCell075.cell.b,MeanAnchor220FastPolynomialCell075.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell076.cell.a,MeanAnchor220FastPolynomialCell076.cell.b,MeanAnchor220FastPolynomialCell076.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell077.cell.a,MeanAnchor220FastPolynomialCell077.cell.b,MeanAnchor220FastPolynomialCell077.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell078.cell.a,MeanAnchor220FastPolynomialCell078.cell.b,MeanAnchor220FastPolynomialCell078.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell079.cell.a,MeanAnchor220FastPolynomialCell079.cell.b,MeanAnchor220FastPolynomialCell079.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell080.cell.a,MeanAnchor220FastPolynomialCell080.cell.b,MeanAnchor220FastPolynomialCell080.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell081.cell.a,MeanAnchor220FastPolynomialCell081.cell.b,MeanAnchor220FastPolynomialCell081.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell082.cell.a,MeanAnchor220FastPolynomialCell082.cell.b,MeanAnchor220FastPolynomialCell082.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell083.cell.a,MeanAnchor220FastPolynomialCell083.cell.b,MeanAnchor220FastPolynomialCell083.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell084.cell.a,MeanAnchor220FastPolynomialCell084.cell.b,MeanAnchor220FastPolynomialCell084.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell085.cell.a,MeanAnchor220FastPolynomialCell085.cell.b,MeanAnchor220FastPolynomialCell085.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell086.cell.a,MeanAnchor220FastPolynomialCell086.cell.b,MeanAnchor220FastPolynomialCell086.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell087.cell.a,MeanAnchor220FastPolynomialCell087.cell.b,MeanAnchor220FastPolynomialCell087.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell088.cell.a,MeanAnchor220FastPolynomialCell088.cell.b,MeanAnchor220FastPolynomialCell088.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell089.cell.a,MeanAnchor220FastPolynomialCell089.cell.b,MeanAnchor220FastPolynomialCell089.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell090.cell.a,MeanAnchor220FastPolynomialCell090.cell.b,MeanAnchor220FastPolynomialCell090.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell091.cell.a,MeanAnchor220FastPolynomialCell091.cell.b,MeanAnchor220FastPolynomialCell091.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell092.cell.a,MeanAnchor220FastPolynomialCell092.cell.b,MeanAnchor220FastPolynomialCell092.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell093.cell.a,MeanAnchor220FastPolynomialCell093.cell.b,MeanAnchor220FastPolynomialCell093.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell094.cell.a,MeanAnchor220FastPolynomialCell094.cell.b,MeanAnchor220FastPolynomialCell094.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell095.cell.a,MeanAnchor220FastPolynomialCell095.cell.b,MeanAnchor220FastPolynomialCell095.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell096.cell.a,MeanAnchor220FastPolynomialCell096.cell.b,MeanAnchor220FastPolynomialCell096.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell097.cell.a,MeanAnchor220FastPolynomialCell097.cell.b,MeanAnchor220FastPolynomialCell097.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell098.cell.a,MeanAnchor220FastPolynomialCell098.cell.b,MeanAnchor220FastPolynomialCell098.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell099.cell.a,MeanAnchor220FastPolynomialCell099.cell.b,MeanAnchor220FastPolynomialCell099.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell100.cell.a,MeanAnchor220FastPolynomialCell100.cell.b,MeanAnchor220FastPolynomialCell100.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell101.cell.a,MeanAnchor220FastPolynomialCell101.cell.b,MeanAnchor220FastPolynomialCell101.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell102.cell.a,MeanAnchor220FastPolynomialCell102.cell.b,MeanAnchor220FastPolynomialCell102.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell103.cell.a,MeanAnchor220FastPolynomialCell103.cell.b,MeanAnchor220FastPolynomialCell103.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell104.cell.a,MeanAnchor220FastPolynomialCell104.cell.b,MeanAnchor220FastPolynomialCell104.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell105.cell.a,MeanAnchor220FastPolynomialCell105.cell.b,MeanAnchor220FastPolynomialCell105.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell106.cell.a,MeanAnchor220FastPolynomialCell106.cell.b,MeanAnchor220FastPolynomialCell106.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell107.cell.a,MeanAnchor220FastPolynomialCell107.cell.b,MeanAnchor220FastPolynomialCell107.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell108.cell.a,MeanAnchor220FastPolynomialCell108.cell.b,MeanAnchor220FastPolynomialCell108.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell109.cell.a,MeanAnchor220FastPolynomialCell109.cell.b,MeanAnchor220FastPolynomialCell109.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell110.cell.a,MeanAnchor220FastPolynomialCell110.cell.b,MeanAnchor220FastPolynomialCell110.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell111.cell.a,MeanAnchor220FastPolynomialCell111.cell.b,MeanAnchor220FastPolynomialCell111.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell112.cell.a,MeanAnchor220FastPolynomialCell112.cell.b,MeanAnchor220FastPolynomialCell112.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell113.cell.a,MeanAnchor220FastPolynomialCell113.cell.b,MeanAnchor220FastPolynomialCell113.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell114.cell.a,MeanAnchor220FastPolynomialCell114.cell.b,MeanAnchor220FastPolynomialCell114.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell115.cell.a,MeanAnchor220FastPolynomialCell115.cell.b,MeanAnchor220FastPolynomialCell115.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell116.cell.a,MeanAnchor220FastPolynomialCell116.cell.b,MeanAnchor220FastPolynomialCell116.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell117.cell.a,MeanAnchor220FastPolynomialCell117.cell.b,MeanAnchor220FastPolynomialCell117.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell118.cell.a,MeanAnchor220FastPolynomialCell118.cell.b,MeanAnchor220FastPolynomialCell118.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell119.cell.a,MeanAnchor220FastPolynomialCell119.cell.b,MeanAnchor220FastPolynomialCell119.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell120.cell.a,MeanAnchor220FastPolynomialCell120.cell.b,MeanAnchor220FastPolynomialCell120.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell121.cell.a,MeanAnchor220FastPolynomialCell121.cell.b,MeanAnchor220FastPolynomialCell121.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell122.cell.a,MeanAnchor220FastPolynomialCell122.cell.b,MeanAnchor220FastPolynomialCell122.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell123.cell.a,MeanAnchor220FastPolynomialCell123.cell.b,MeanAnchor220FastPolynomialCell123.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell124.cell.a,MeanAnchor220FastPolynomialCell124.cell.b,MeanAnchor220FastPolynomialCell124.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell125.cell.a,MeanAnchor220FastPolynomialCell125.cell.b,MeanAnchor220FastPolynomialCell125.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell126.cell.a,MeanAnchor220FastPolynomialCell126.cell.b,MeanAnchor220FastPolynomialCell126.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell127.cell.a,MeanAnchor220FastPolynomialCell127.cell.b,MeanAnchor220FastPolynomialCell127.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell128.cell.a,MeanAnchor220FastPolynomialCell128.cell.b,MeanAnchor220FastPolynomialCell128.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell129.cell.a,MeanAnchor220FastPolynomialCell129.cell.b,MeanAnchor220FastPolynomialCell129.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell130.cell.a,MeanAnchor220FastPolynomialCell130.cell.b,MeanAnchor220FastPolynomialCell130.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell131.cell.a,MeanAnchor220FastPolynomialCell131.cell.b,MeanAnchor220FastPolynomialCell131.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell132.cell.a,MeanAnchor220FastPolynomialCell132.cell.b,MeanAnchor220FastPolynomialCell132.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell133.cell.a,MeanAnchor220FastPolynomialCell133.cell.b,MeanAnchor220FastPolynomialCell133.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell134.cell.a,MeanAnchor220FastPolynomialCell134.cell.b,MeanAnchor220FastPolynomialCell134.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell135.cell.a,MeanAnchor220FastPolynomialCell135.cell.b,MeanAnchor220FastPolynomialCell135.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell136.cell.a,MeanAnchor220FastPolynomialCell136.cell.b,MeanAnchor220FastPolynomialCell136.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell137.cell.a,MeanAnchor220FastPolynomialCell137.cell.b,MeanAnchor220FastPolynomialCell137.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell138.cell.a,MeanAnchor220FastPolynomialCell138.cell.b,MeanAnchor220FastPolynomialCell138.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell139.cell.a,MeanAnchor220FastPolynomialCell139.cell.b,MeanAnchor220FastPolynomialCell139.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell140.cell.a,MeanAnchor220FastPolynomialCell140.cell.b,MeanAnchor220FastPolynomialCell140.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell141.cell.a,MeanAnchor220FastPolynomialCell141.cell.b,MeanAnchor220FastPolynomialCell141.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell142.cell.a,MeanAnchor220FastPolynomialCell142.cell.b,MeanAnchor220FastPolynomialCell142.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell143.cell.a,MeanAnchor220FastPolynomialCell143.cell.b,MeanAnchor220FastPolynomialCell143.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell144.cell.a,MeanAnchor220FastPolynomialCell144.cell.b,MeanAnchor220FastPolynomialCell144.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell145.cell.a,MeanAnchor220FastPolynomialCell145.cell.b,MeanAnchor220FastPolynomialCell145.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell146.cell.a,MeanAnchor220FastPolynomialCell146.cell.b,MeanAnchor220FastPolynomialCell146.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell147.cell.a,MeanAnchor220FastPolynomialCell147.cell.b,MeanAnchor220FastPolynomialCell147.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell148.cell.a,MeanAnchor220FastPolynomialCell148.cell.b,MeanAnchor220FastPolynomialCell148.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell149.cell.a,MeanAnchor220FastPolynomialCell149.cell.b,MeanAnchor220FastPolynomialCell149.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell150.cell.a,MeanAnchor220FastPolynomialCell150.cell.b,MeanAnchor220FastPolynomialCell150.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell151.cell.a,MeanAnchor220FastPolynomialCell151.cell.b,MeanAnchor220FastPolynomialCell151.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell152.cell.a,MeanAnchor220FastPolynomialCell152.cell.b,MeanAnchor220FastPolynomialCell152.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell153.cell.a,MeanAnchor220FastPolynomialCell153.cell.b,MeanAnchor220FastPolynomialCell153.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell154.cell.a,MeanAnchor220FastPolynomialCell154.cell.b,MeanAnchor220FastPolynomialCell154.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell155.cell.a,MeanAnchor220FastPolynomialCell155.cell.b,MeanAnchor220FastPolynomialCell155.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell156.cell.a,MeanAnchor220FastPolynomialCell156.cell.b,MeanAnchor220FastPolynomialCell156.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell157.cell.a,MeanAnchor220FastPolynomialCell157.cell.b,MeanAnchor220FastPolynomialCell157.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell158.cell.a,MeanAnchor220FastPolynomialCell158.cell.b,MeanAnchor220FastPolynomialCell158.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell159.cell.a,MeanAnchor220FastPolynomialCell159.cell.b,MeanAnchor220FastPolynomialCell159.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell160.cell.a,MeanAnchor220FastPolynomialCell160.cell.b,MeanAnchor220FastPolynomialCell160.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell161.cell.a,MeanAnchor220FastPolynomialCell161.cell.b,MeanAnchor220FastPolynomialCell161.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell162.cell.a,MeanAnchor220FastPolynomialCell162.cell.b,MeanAnchor220FastPolynomialCell162.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell163.cell.a,MeanAnchor220FastPolynomialCell163.cell.b,MeanAnchor220FastPolynomialCell163.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell164.cell.a,MeanAnchor220FastPolynomialCell164.cell.b,MeanAnchor220FastPolynomialCell164.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell165.cell.a,MeanAnchor220FastPolynomialCell165.cell.b,MeanAnchor220FastPolynomialCell165.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell166.cell.a,MeanAnchor220FastPolynomialCell166.cell.b,MeanAnchor220FastPolynomialCell166.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell167.cell.a,MeanAnchor220FastPolynomialCell167.cell.b,MeanAnchor220FastPolynomialCell167.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell168.cell.a,MeanAnchor220FastPolynomialCell168.cell.b,MeanAnchor220FastPolynomialCell168.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell169.cell.a,MeanAnchor220FastPolynomialCell169.cell.b,MeanAnchor220FastPolynomialCell169.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell170.cell.a,MeanAnchor220FastPolynomialCell170.cell.b,MeanAnchor220FastPolynomialCell170.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell171.cell.a,MeanAnchor220FastPolynomialCell171.cell.b,MeanAnchor220FastPolynomialCell171.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell172.cell.a,MeanAnchor220FastPolynomialCell172.cell.b,MeanAnchor220FastPolynomialCell172.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell173.cell.a,MeanAnchor220FastPolynomialCell173.cell.b,MeanAnchor220FastPolynomialCell173.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell174.cell.a,MeanAnchor220FastPolynomialCell174.cell.b,MeanAnchor220FastPolynomialCell174.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell175.cell.a,MeanAnchor220FastPolynomialCell175.cell.b,MeanAnchor220FastPolynomialCell175.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell176.cell.a,MeanAnchor220FastPolynomialCell176.cell.b,MeanAnchor220FastPolynomialCell176.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell177.cell.a,MeanAnchor220FastPolynomialCell177.cell.b,MeanAnchor220FastPolynomialCell177.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell178.cell.a,MeanAnchor220FastPolynomialCell178.cell.b,MeanAnchor220FastPolynomialCell178.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell179.cell.a,MeanAnchor220FastPolynomialCell179.cell.b,MeanAnchor220FastPolynomialCell179.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell180.cell.a,MeanAnchor220FastPolynomialCell180.cell.b,MeanAnchor220FastPolynomialCell180.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell181.cell.a,MeanAnchor220FastPolynomialCell181.cell.b,MeanAnchor220FastPolynomialCell181.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell182.cell.a,MeanAnchor220FastPolynomialCell182.cell.b,MeanAnchor220FastPolynomialCell182.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell183.cell.a,MeanAnchor220FastPolynomialCell183.cell.b,MeanAnchor220FastPolynomialCell183.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell184.cell.a,MeanAnchor220FastPolynomialCell184.cell.b,MeanAnchor220FastPolynomialCell184.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell185.cell.a,MeanAnchor220FastPolynomialCell185.cell.b,MeanAnchor220FastPolynomialCell185.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell186.cell.a,MeanAnchor220FastPolynomialCell186.cell.b,MeanAnchor220FastPolynomialCell186.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell187.cell.a,MeanAnchor220FastPolynomialCell187.cell.b,MeanAnchor220FastPolynomialCell187.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell188.cell.a,MeanAnchor220FastPolynomialCell188.cell.b,MeanAnchor220FastPolynomialCell188.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell189.cell.a,MeanAnchor220FastPolynomialCell189.cell.b,MeanAnchor220FastPolynomialCell189.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell190.cell.a,MeanAnchor220FastPolynomialCell190.cell.b,MeanAnchor220FastPolynomialCell190.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell191.cell.a,MeanAnchor220FastPolynomialCell191.cell.b,MeanAnchor220FastPolynomialCell191.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell192.cell.a,MeanAnchor220FastPolynomialCell192.cell.b,MeanAnchor220FastPolynomialCell192.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell193.cell.a,MeanAnchor220FastPolynomialCell193.cell.b,MeanAnchor220FastPolynomialCell193.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell194.cell.a,MeanAnchor220FastPolynomialCell194.cell.b,MeanAnchor220FastPolynomialCell194.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell195.cell.a,MeanAnchor220FastPolynomialCell195.cell.b,MeanAnchor220FastPolynomialCell195.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell196.cell.a,MeanAnchor220FastPolynomialCell196.cell.b,MeanAnchor220FastPolynomialCell196.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell197.cell.a,MeanAnchor220FastPolynomialCell197.cell.b,MeanAnchor220FastPolynomialCell197.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell198.cell.a,MeanAnchor220FastPolynomialCell198.cell.b,MeanAnchor220FastPolynomialCell198.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell199.cell.a,MeanAnchor220FastPolynomialCell199.cell.b,MeanAnchor220FastPolynomialCell199.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell200.cell.a,MeanAnchor220FastPolynomialCell200.cell.b,MeanAnchor220FastPolynomialCell200.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell201.cell.a,MeanAnchor220FastPolynomialCell201.cell.b,MeanAnchor220FastPolynomialCell201.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell202.cell.a,MeanAnchor220FastPolynomialCell202.cell.b,MeanAnchor220FastPolynomialCell202.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell203.cell.a,MeanAnchor220FastPolynomialCell203.cell.b,MeanAnchor220FastPolynomialCell203.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell204.cell.a,MeanAnchor220FastPolynomialCell204.cell.b,MeanAnchor220FastPolynomialCell204.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell205.cell.a,MeanAnchor220FastPolynomialCell205.cell.b,MeanAnchor220FastPolynomialCell205.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell206.cell.a,MeanAnchor220FastPolynomialCell206.cell.b,MeanAnchor220FastPolynomialCell206.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell207.cell.a,MeanAnchor220FastPolynomialCell207.cell.b,MeanAnchor220FastPolynomialCell207.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell208.cell.a,MeanAnchor220FastPolynomialCell208.cell.b,MeanAnchor220FastPolynomialCell208.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell209.cell.a,MeanAnchor220FastPolynomialCell209.cell.b,MeanAnchor220FastPolynomialCell209.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell210.cell.a,MeanAnchor220FastPolynomialCell210.cell.b,MeanAnchor220FastPolynomialCell210.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell211.cell.a,MeanAnchor220FastPolynomialCell211.cell.b,MeanAnchor220FastPolynomialCell211.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell212.cell.a,MeanAnchor220FastPolynomialCell212.cell.b,MeanAnchor220FastPolynomialCell212.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell213.cell.a,MeanAnchor220FastPolynomialCell213.cell.b,MeanAnchor220FastPolynomialCell213.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell214.cell.a,MeanAnchor220FastPolynomialCell214.cell.b,MeanAnchor220FastPolynomialCell214.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell215.cell.a,MeanAnchor220FastPolynomialCell215.cell.b,MeanAnchor220FastPolynomialCell215.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell216.cell.a,MeanAnchor220FastPolynomialCell216.cell.b,MeanAnchor220FastPolynomialCell216.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell217.cell.a,MeanAnchor220FastPolynomialCell217.cell.b,MeanAnchor220FastPolynomialCell217.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell218.cell.a,MeanAnchor220FastPolynomialCell218.cell.b,MeanAnchor220FastPolynomialCell218.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell219.cell.a,MeanAnchor220FastPolynomialCell219.cell.b,MeanAnchor220FastPolynomialCell219.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell220.cell.a,MeanAnchor220FastPolynomialCell220.cell.b,MeanAnchor220FastPolynomialCell220.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell221.cell.a,MeanAnchor220FastPolynomialCell221.cell.b,MeanAnchor220FastPolynomialCell221.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell222.cell.a,MeanAnchor220FastPolynomialCell222.cell.b,MeanAnchor220FastPolynomialCell222.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell223.cell.a,MeanAnchor220FastPolynomialCell223.cell.b,MeanAnchor220FastPolynomialCell223.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell224.cell.a,MeanAnchor220FastPolynomialCell224.cell.b,MeanAnchor220FastPolynomialCell224.cell.total⟩,
  ⟨MeanAnchor220FastPolynomialCell225.cell.a,MeanAnchor220FastPolynomialCell225.cell.b,MeanAnchor220FastPolynomialCell225.cell.total⟩
]
def payment : ℚ := (142858522873449/1000000000000000)

theorem chain_checked : check (1/16777216) 128 slices = true := by decide +kernel
theorem total_checked : total slices = payment := by decide +kernel

theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u = 1) :
    (payment : ℝ) ≤ ∫ y : ℝ in (1/16777216 : ℝ)..128,
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 0)
        (CoreQuotient.fused G u 0 0) (51/26) y := by
  let f := MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 0) (CoreQuotient.fused G u 0 0) (51/26)
  have hf := ActualFusionIntegral.logarithm_integrable G u 0 0 (51/26)
  have hp : ∀ c ∈ slices, (c.payment : ℝ) ≤ ∫ y : ℝ in (c.a : ℝ)..(c.b : ℝ), f y := by
    intro c hc
    simp only [slices,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact MeanAnchor220FastPolynomialCell000.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell001.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell002.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell003.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell004.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell005.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell006.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell007.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell008.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell009.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell010.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell011.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell012.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell013.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell014.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell015.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell016.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell017.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell018.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell019.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell020.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell021.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell022.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell023.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell024.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell025.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell026.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell027.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell028.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell029.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell030.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell031.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell032.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell033.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell034.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell035.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell036.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell037.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell038.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell039.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell040.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell041.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell042.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell043.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell044.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell045.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell046.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell047.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell048.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell049.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell050.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell051.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell052.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell053.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell054.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell055.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell056.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell057.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell058.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell059.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell060.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell061.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell062.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell063.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell064.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell065.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell066.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell067.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell068.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell069.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell070.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell071.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell072.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell073.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell074.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell075.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell076.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell077.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell078.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell079.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell080.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell081.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell082.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell083.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell084.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell085.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell086.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell087.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell088.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell089.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell090.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell091.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell092.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell093.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell094.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell095.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell096.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell097.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell098.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell099.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell100.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell101.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell102.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell103.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell104.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell105.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell106.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell107.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell108.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell109.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell110.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell111.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell112.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell113.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell114.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell115.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell116.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell117.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell118.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell119.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell120.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell121.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell122.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell123.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell124.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell125.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell126.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell127.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell128.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell129.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell130.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell131.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell132.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell133.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell134.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell135.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell136.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell137.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell138.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell139.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell140.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell141.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell142.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell143.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell144.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell145.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell146.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell147.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell148.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell149.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell150.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell151.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell152.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell153.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell154.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell155.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell156.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell157.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell158.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell159.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell160.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell161.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell162.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell163.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell164.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell165.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell166.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell167.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell168.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell169.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell170.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell171.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell172.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell173.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell174.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell175.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell176.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell177.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell178.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell179.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell180.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell181.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell182.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell183.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell184.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell185.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell186.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell187.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell188.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell189.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell190.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell191.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell192.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell193.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell194.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell195.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell196.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell197.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell198.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell199.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell200.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell201.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell202.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell203.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell204.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell205.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell206.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell207.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell208.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell209.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell210.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell211.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell212.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell213.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell214.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell215.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell216.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell217.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell218.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell219.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell220.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell221.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell222.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell223.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell224.actual_integral G u hd
    · exact MeanAnchor220FastPolynomialCell225.actual_integral G u hd
  have h := RationalIntegralPartition.integral_lower f hf (1/16777216) 128 slices
    (by norm_num) chain_checked hp
  rw [total_checked] at h
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h

#print axioms chain_checked
#print axioms total_checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.MeanAnchor220FinitePayment
