/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2474 : Family 10 := level10.get ⟨113,by decide⟩
def sourceMap2474 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2474 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2474_checked : acceptsGraphIso
    (source (graph core2474) (root 10) 0 4) DegreeTwoThreeSpectrum5644.graph sourceMap2474=true := by decide +kernel
theorem fusedMap2474_checked : acceptsGraphIso
    (fused (graph core2474) (root 10) 0 4) DegreeTwoThreeSpectrum5037.graph fusedMap2474=true := by decide +kernel
theorem certified2474 : Certified (graph core2474) (root 10) 0 4 :=
  of_native_maps core2474 DegreeTwoThreeSpectrum5644.graph DegreeTwoThreeSpectrum5037.graph
    sourceMap2474 fusedMap2474 sourceMap2474_checked fusedMap2474_checked
    DegreeTwoThreeFiniteComparisons.comparison2474
#print axioms sourceMap2474_checked
#print axioms fusedMap2474_checked
#print axioms certified2474
def sourceMap2474swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2474swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2474swap_checked : acceptsGraphIso
    (source (graph core2474) (root 10) 4 0) DegreeTwoThreeSpectrum5644.graph sourceMap2474swap=true := by decide +kernel
theorem fusedMap2474swap_checked : acceptsGraphIso
    (fused (graph core2474) (root 10) 4 0) DegreeTwoThreeSpectrum5037.graph fusedMap2474swap=true := by decide +kernel
theorem certified2474swap : Certified (graph core2474) (root 10) 4 0 :=
  of_native_maps core2474 DegreeTwoThreeSpectrum5644.graph DegreeTwoThreeSpectrum5037.graph
    sourceMap2474swap fusedMap2474swap sourceMap2474swap_checked fusedMap2474swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2474
#print axioms sourceMap2474swap_checked
#print axioms fusedMap2474swap_checked
#print axioms certified2474swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
