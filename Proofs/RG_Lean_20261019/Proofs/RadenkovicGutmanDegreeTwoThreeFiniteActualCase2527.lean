/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2527 : Family 10 := level10.get ⟨302,by decide⟩
def sourceMap2527 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2527 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2527_checked : acceptsGraphIso
    (source (graph core2527) (root 10) 0 4) DegreeTwoThreeSpectrum5478.graph sourceMap2527=true := by decide +kernel
theorem fusedMap2527_checked : acceptsGraphIso
    (fused (graph core2527) (root 10) 0 4) DegreeTwoThreeSpectrum5480.graph fusedMap2527=true := by decide +kernel
theorem certified2527 : Certified (graph core2527) (root 10) 0 4 :=
  of_native_maps core2527 DegreeTwoThreeSpectrum5478.graph DegreeTwoThreeSpectrum5480.graph
    sourceMap2527 fusedMap2527 sourceMap2527_checked fusedMap2527_checked
    DegreeTwoThreeFiniteComparisons.comparison2527
#print axioms sourceMap2527_checked
#print axioms fusedMap2527_checked
#print axioms certified2527
def sourceMap2527swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2527swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2527swap_checked : acceptsGraphIso
    (source (graph core2527) (root 10) 4 0) DegreeTwoThreeSpectrum5478.graph sourceMap2527swap=true := by decide +kernel
theorem fusedMap2527swap_checked : acceptsGraphIso
    (fused (graph core2527) (root 10) 4 0) DegreeTwoThreeSpectrum5480.graph fusedMap2527swap=true := by decide +kernel
theorem certified2527swap : Certified (graph core2527) (root 10) 4 0 :=
  of_native_maps core2527 DegreeTwoThreeSpectrum5478.graph DegreeTwoThreeSpectrum5480.graph
    sourceMap2527swap fusedMap2527swap sourceMap2527swap_checked fusedMap2527swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2527
#print axioms sourceMap2527swap_checked
#print axioms fusedMap2527swap_checked
#print axioms certified2527swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
