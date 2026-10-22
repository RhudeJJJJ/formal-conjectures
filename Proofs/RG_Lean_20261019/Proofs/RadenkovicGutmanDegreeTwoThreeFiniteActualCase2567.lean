/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2567 : Family 10 := level10.get ⟨437,by decide⟩
def sourceMap2567 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2567 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2567_checked : acceptsGraphIso
    (source (graph core2567) (root 10) 0 4) DegreeTwoThreeSpectrum5848.graph sourceMap2567=true := by decide +kernel
theorem fusedMap2567_checked : acceptsGraphIso
    (fused (graph core2567) (root 10) 0 4) DegreeTwoThreeSpectrum5849.graph fusedMap2567=true := by decide +kernel
theorem certified2567 : Certified (graph core2567) (root 10) 0 4 :=
  of_native_maps core2567 DegreeTwoThreeSpectrum5848.graph DegreeTwoThreeSpectrum5849.graph
    sourceMap2567 fusedMap2567 sourceMap2567_checked fusedMap2567_checked
    DegreeTwoThreeFiniteComparisons.comparison2567
#print axioms sourceMap2567_checked
#print axioms fusedMap2567_checked
#print axioms certified2567
def sourceMap2567swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2567swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2567swap_checked : acceptsGraphIso
    (source (graph core2567) (root 10) 4 0) DegreeTwoThreeSpectrum5848.graph sourceMap2567swap=true := by decide +kernel
theorem fusedMap2567swap_checked : acceptsGraphIso
    (fused (graph core2567) (root 10) 4 0) DegreeTwoThreeSpectrum5849.graph fusedMap2567swap=true := by decide +kernel
theorem certified2567swap : Certified (graph core2567) (root 10) 4 0 :=
  of_native_maps core2567 DegreeTwoThreeSpectrum5848.graph DegreeTwoThreeSpectrum5849.graph
    sourceMap2567swap fusedMap2567swap sourceMap2567swap_checked fusedMap2567swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2567
#print axioms sourceMap2567swap_checked
#print axioms fusedMap2567swap_checked
#print axioms certified2567swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
