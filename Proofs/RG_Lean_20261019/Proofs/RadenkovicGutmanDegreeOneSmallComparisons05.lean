/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum027
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum034
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum035
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum036
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum037
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum048
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum051
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum052
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum066
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum073
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum078
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum080
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum084
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum085
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum086
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum090
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum093
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1275
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1365
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1370
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1439
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum1464
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum155
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum164
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum165
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum166
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum168
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum190
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum196
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum200
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum201
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum202
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum207
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum216
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum226
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum235
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum239
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum337
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum369
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum377
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum378
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum380
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum385
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum386
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum387
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum391
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum392
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum396
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum399
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum494
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum524
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum555
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum608
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum808
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum824
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum856
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum857
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum858
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum860
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum861
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum862
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum905
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum908
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum922
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum941
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum944
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum945
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum966
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum971
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum986
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum992
import Proofs.RadenkovicGutmanSmallGeFourSpectrum003
import Proofs.RadenkovicGutmanSmallGeFourSpectrum006
import Proofs.RadenkovicGutmanSmallGeFourSpectrum016
import Proofs.RadenkovicGutmanSmallGeFourSpectrum037
import Proofs.RadenkovicGutmanSmallGeFourSpectrum094
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison0250 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum207.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum337.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum337.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum207.actual_graph_bounds.2
  linarith
#print axioms comparison0250
theorem comparison0251 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum380.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum524.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum524.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum380.actual_graph_bounds.2
  linarith
#print axioms comparison0251
theorem comparison0252 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum922.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1370.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1370.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum922.actual_graph_bounds.2
  linarith
#print axioms comparison0252
theorem comparison0253 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum380.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum808.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum808.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum380.actual_graph_bounds.2
  linarith
#print axioms comparison0253
theorem comparison0254 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum922.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1365.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1365.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum922.actual_graph_bounds.2
  linarith
#print axioms comparison0254
theorem comparison0255 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum003.graph) (2-2/8) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum027.graph) (2-2/8) := by
  have hs := DegreeOneSmallSpectrum027.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum003.actual_graph_bounds.2
  linarith
#print axioms comparison0255
theorem comparison0256 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum006.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum066.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum066.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum006.actual_graph_bounds.2
  linarith
#print axioms comparison0256
theorem comparison0257 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum016.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum093.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum093.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum016.actual_graph_bounds.2
  linarith
#print axioms comparison0257
theorem comparison0258 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum037.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum239.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum239.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0258
theorem comparison0259 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum094.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum399.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum399.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum094.actual_graph_bounds.2
  linarith
#print axioms comparison0259
theorem comparison0260 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum862.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum992.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum992.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum862.actual_graph_bounds.2
  linarith
#print axioms comparison0260
theorem comparison0261 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum016.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum155.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum155.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum016.actual_graph_bounds.2
  linarith
#print axioms comparison0261
theorem comparison0262 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum037.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum235.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum235.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0262
theorem comparison0263 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum094.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum608.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum608.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum094.actual_graph_bounds.2
  linarith
#print axioms comparison0263
theorem comparison0264 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum862.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum986.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum986.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum862.actual_graph_bounds.2
  linarith
#print axioms comparison0264
theorem comparison0265 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum094.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum824.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum824.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum094.actual_graph_bounds.2
  linarith
#print axioms comparison0265
theorem comparison0266 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum862.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1464.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1464.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum862.actual_graph_bounds.2
  linarith
#print axioms comparison0266
theorem comparison0267 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum037.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum034.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum034.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison0267
theorem comparison0268 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum073.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum086.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum086.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum073.actual_graph_bounds.2
  linarith
#print axioms comparison0268
theorem comparison0269 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum166.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum166.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0269
theorem comparison0270 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum396.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum396.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0270
theorem comparison0271 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum860.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum860.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0271
theorem comparison0272 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum168.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum202.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum202.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum168.actual_graph_bounds.2
  linarith
#print axioms comparison0272
theorem comparison0273 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum369.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum387.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum387.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum369.actual_graph_bounds.2
  linarith
#print axioms comparison0273
theorem comparison0274 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum971.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum971.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0274
theorem comparison0275 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum861.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum945.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum945.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum861.actual_graph_bounds.2
  linarith
#print axioms comparison0275
theorem comparison0276 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum034.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum048.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum048.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum034.actual_graph_bounds.2
  linarith
#print axioms comparison0276
theorem comparison0277 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum080.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum078.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum078.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum080.actual_graph_bounds.2
  linarith
#print axioms comparison0277
theorem comparison0278 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum164.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum196.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum196.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum164.actual_graph_bounds.2
  linarith
#print axioms comparison0278
theorem comparison0279 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum378.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum377.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum377.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum378.actual_graph_bounds.2
  linarith
#print axioms comparison0279
theorem comparison0280 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum908.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum908.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0280
theorem comparison0281 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum164.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum190.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum190.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum164.actual_graph_bounds.2
  linarith
#print axioms comparison0281
theorem comparison0282 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum378.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum494.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum494.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum378.actual_graph_bounds.2
  linarith
#print axioms comparison0282
theorem comparison0283 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum905.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum905.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0283
theorem comparison0284 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum856.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1275.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1275.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum856.actual_graph_bounds.2
  linarith
#print axioms comparison0284
theorem comparison0285 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum035.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum051.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum051.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum035.actual_graph_bounds.2
  linarith
#print axioms comparison0285
theorem comparison0286 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum086.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum084.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum084.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum086.actual_graph_bounds.2
  linarith
#print axioms comparison0286
theorem comparison0287 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum165.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum216.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum216.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum165.actual_graph_bounds.2
  linarith
#print axioms comparison0287
theorem comparison0288 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum386.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum385.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum385.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum386.actual_graph_bounds.2
  linarith
#print axioms comparison0288
theorem comparison0289 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum944.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum944.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum857.actual_graph_bounds.2
  linarith
#print axioms comparison0289
theorem comparison0290 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum165.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum200.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum200.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum165.actual_graph_bounds.2
  linarith
#print axioms comparison0290
theorem comparison0291 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum386.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum555.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum555.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum386.actual_graph_bounds.2
  linarith
#print axioms comparison0291
theorem comparison0292 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum941.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum941.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum857.actual_graph_bounds.2
  linarith
#print axioms comparison0292
theorem comparison0293 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum1439.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum1439.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum857.actual_graph_bounds.2
  linarith
#print axioms comparison0293
theorem comparison0294 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum036.graph) (2-2/9) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum052.graph) (2-2/9) := by
  have hs := DegreeOneSmallSpectrum052.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum036.actual_graph_bounds.2
  linarith
#print axioms comparison0294
theorem comparison0295 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum090.graph) (2-2/10) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum085.graph) (2-2/10) := by
  have hs := DegreeOneSmallSpectrum085.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum090.actual_graph_bounds.2
  linarith
#print axioms comparison0295
theorem comparison0296 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum166.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum226.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum226.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum166.actual_graph_bounds.2
  linarith
#print axioms comparison0296
theorem comparison0297 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum392.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum391.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum391.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum392.actual_graph_bounds.2
  linarith
#print axioms comparison0297
theorem comparison0298 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum858.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum966.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum966.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum858.actual_graph_bounds.2
  linarith
#print axioms comparison0298
theorem comparison0299 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum166.graph) (2-2/11) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum201.graph) (2-2/11) := by
  have hs := DegreeOneSmallSpectrum201.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum166.actual_graph_bounds.2
  linarith
#print axioms comparison0299
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
