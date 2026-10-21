/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum017
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum018
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum022
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum023
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum029
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum031
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum032
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum033
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum041
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum042
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum046
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum047
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum054
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum055
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum057
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum058
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum074
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum075
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum081
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum082
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum090
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1038
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum104
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1044
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum106
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1136
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1142
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum118
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum121
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1314
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1319
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum134
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum135
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum137
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum142
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1504
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum166
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum171
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum175
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum178
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum182
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum199
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum202
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum204
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum207
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum221
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum265
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum299
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum329
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum370
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum371
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum379
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum380
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum392
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum412
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum417
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum441
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum446
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum506
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum510
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum528
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum562
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum583
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum669
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum741
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum794
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum858
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum864
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum870
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum873
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum879
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum910
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum915
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum917
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum922
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum957
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum961
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0200 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum858.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum961.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum961.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum858.actual_graph_bounds.2
  linarith
#print axioms comparison0200
theorem comparison0201 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum090.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum137.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum137.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum090.actual_graph_bounds.2
  linarith
#print axioms comparison0201
theorem comparison0202 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum166.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum221.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum221.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum166.actual_graph_bounds.2
  linarith
#print axioms comparison0202
theorem comparison0203 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum392.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum583.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum583.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum392.actual_graph_bounds.2
  linarith
#print axioms comparison0203
theorem comparison0204 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum858.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum957.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum957.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum858.actual_graph_bounds.2
  linarith
#print axioms comparison0204
theorem comparison0205 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum392.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum562.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum562.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum392.actual_graph_bounds.2
  linarith
#print axioms comparison0205
theorem comparison0206 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum858.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1504.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1504.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum858.actual_graph_bounds.2
  linarith
#print axioms comparison0206
theorem comparison0207 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum017.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum029.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum029.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum017.actual_graph_bounds.2
  linarith
#print axioms comparison0207
theorem comparison0208 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum042.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum041.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum041.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum042.actual_graph_bounds.2
  linarith
#print axioms comparison0208
theorem comparison0209 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum074.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum106.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum106.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum074.actual_graph_bounds.2
  linarith
#print axioms comparison0209
theorem comparison0210 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum175.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum171.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum171.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum175.actual_graph_bounds.2
  linarith
#print axioms comparison0210
theorem comparison0211 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum370.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum417.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum417.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum370.actual_graph_bounds.2
  linarith
#print axioms comparison0211
theorem comparison0212 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum864.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum864.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison0212
theorem comparison0213 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum074.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum104.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum104.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum074.actual_graph_bounds.2
  linarith
#print axioms comparison0213
theorem comparison0214 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum175.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum265.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum265.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum175.actual_graph_bounds.2
  linarith
#print axioms comparison0214
theorem comparison0215 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum370.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum412.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum412.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum370.actual_graph_bounds.2
  linarith
#print axioms comparison0215
theorem comparison0216 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1044.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1044.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison0216
theorem comparison0217 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum370.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum669.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum669.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum370.actual_graph_bounds.2
  linarith
#print axioms comparison0217
theorem comparison0218 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1038.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1038.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison0218
theorem comparison0219 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum018.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum031.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum031.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum018.actual_graph_bounds.2
  linarith
#print axioms comparison0219
theorem comparison0220 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum047.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum046.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum046.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum047.actual_graph_bounds.2
  linarith
#print axioms comparison0220
theorem comparison0221 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum075.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum121.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum121.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum075.actual_graph_bounds.2
  linarith
#print axioms comparison0221
theorem comparison0222 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum182.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum178.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum178.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum182.actual_graph_bounds.2
  linarith
#print axioms comparison0222
theorem comparison0223 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum371.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum446.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum446.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum371.actual_graph_bounds.2
  linarith
#print axioms comparison0223
theorem comparison0224 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum879.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum873.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum873.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum879.actual_graph_bounds.2
  linarith
#print axioms comparison0224
theorem comparison0225 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum075.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum118.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum118.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum075.actual_graph_bounds.2
  linarith
#print axioms comparison0225
theorem comparison0226 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum182.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum299.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum299.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum182.actual_graph_bounds.2
  linarith
#print axioms comparison0226
theorem comparison0227 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum371.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum441.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum441.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum371.actual_graph_bounds.2
  linarith
#print axioms comparison0227
theorem comparison0228 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum879.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1142.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1142.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum879.actual_graph_bounds.2
  linarith
#print axioms comparison0228
theorem comparison0229 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum371.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum741.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum741.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum371.actual_graph_bounds.2
  linarith
#print axioms comparison0229
theorem comparison0230 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum879.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1136.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1136.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum879.actual_graph_bounds.2
  linarith
#print axioms comparison0230
theorem comparison0231 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum022.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum032.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum032.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum022.actual_graph_bounds.2
  linarith
#print axioms comparison0231
theorem comparison0232 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum055.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum054.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum054.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum055.actual_graph_bounds.2
  linarith
#print axioms comparison0232
theorem comparison0233 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum081.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum137.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum137.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum081.actual_graph_bounds.2
  linarith
#print axioms comparison0233
theorem comparison0234 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum202.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum199.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum199.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum202.actual_graph_bounds.2
  linarith
#print axioms comparison0234
theorem comparison0235 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum379.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum510.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum510.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum379.actual_graph_bounds.2
  linarith
#print axioms comparison0235
theorem comparison0236 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum915.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum910.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum910.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum915.actual_graph_bounds.2
  linarith
#print axioms comparison0236
theorem comparison0237 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum081.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum134.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum134.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum081.actual_graph_bounds.2
  linarith
#print axioms comparison0237
theorem comparison0238 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum202.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum329.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum329.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum202.actual_graph_bounds.2
  linarith
#print axioms comparison0238
theorem comparison0239 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum379.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum506.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum506.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum379.actual_graph_bounds.2
  linarith
#print axioms comparison0239
theorem comparison0240 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum915.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1319.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1319.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum915.actual_graph_bounds.2
  linarith
#print axioms comparison0240
theorem comparison0241 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum379.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum794.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum794.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum379.actual_graph_bounds.2
  linarith
#print axioms comparison0241
theorem comparison0242 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum915.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1314.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1314.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum915.actual_graph_bounds.2
  linarith
#print axioms comparison0242
theorem comparison0243 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum023.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum033.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum033.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum023.actual_graph_bounds.2
  linarith
#print axioms comparison0243
theorem comparison0244 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum058.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum057.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum057.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum058.actual_graph_bounds.2
  linarith
#print axioms comparison0244
theorem comparison0245 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum082.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum142.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum142.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum082.actual_graph_bounds.2
  linarith
#print axioms comparison0245
theorem comparison0246 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum207.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum204.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum204.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum207.actual_graph_bounds.2
  linarith
#print axioms comparison0246
theorem comparison0247 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum380.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum528.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum528.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum380.actual_graph_bounds.2
  linarith
#print axioms comparison0247
theorem comparison0248 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum922.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum917.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum917.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum922.actual_graph_bounds.2
  linarith
#print axioms comparison0248
theorem comparison0249 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum082.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum135.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum135.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum082.actual_graph_bounds.2
  linarith
#print axioms comparison0249
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
