/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2467 : Family 10 := level10.get ⟨81,by decide⟩
def sourceMap2467 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2467 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2467_checked : acceptsGraphIso
    (source (graph core2467) (root 10) 0 4) DegreeTwoThreeSpectrum5410.graph sourceMap2467=true := by decide +kernel
theorem fusedMap2467_checked : acceptsGraphIso
    (fused (graph core2467) (root 10) 0 4) DegreeTwoThreeSpectrum4997.graph fusedMap2467=true := by decide +kernel
theorem certified2467 : Certified (graph core2467) (root 10) 0 4 :=
  of_native_maps core2467 DegreeTwoThreeSpectrum5410.graph DegreeTwoThreeSpectrum4997.graph
    sourceMap2467 fusedMap2467 sourceMap2467_checked fusedMap2467_checked
    DegreeTwoThreeFiniteComparisons.comparison2467
#print axioms sourceMap2467_checked
#print axioms fusedMap2467_checked
#print axioms certified2467
def sourceMap2467swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2467swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2467swap_checked : acceptsGraphIso
    (source (graph core2467) (root 10) 4 0) DegreeTwoThreeSpectrum5410.graph sourceMap2467swap=true := by decide +kernel
theorem fusedMap2467swap_checked : acceptsGraphIso
    (fused (graph core2467) (root 10) 4 0) DegreeTwoThreeSpectrum4997.graph fusedMap2467swap=true := by decide +kernel
theorem certified2467swap : Certified (graph core2467) (root 10) 4 0 :=
  of_native_maps core2467 DegreeTwoThreeSpectrum5410.graph DegreeTwoThreeSpectrum4997.graph
    sourceMap2467swap fusedMap2467swap sourceMap2467swap_checked fusedMap2467swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2467
#print axioms sourceMap2467swap_checked
#print axioms fusedMap2467swap_checked
#print axioms certified2467swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
