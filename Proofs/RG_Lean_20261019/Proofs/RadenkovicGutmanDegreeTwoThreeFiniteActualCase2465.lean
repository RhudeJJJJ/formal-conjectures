/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2465 : Family 10 := level10.get ⟨72,by decide⟩
def sourceMap2465 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2465 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2465_checked : acceptsGraphIso
    (source (graph core2465) (root 10) 0 4) DegreeTwoThreeSpectrum5359.graph sourceMap2465=true := by decide +kernel
theorem fusedMap2465_checked : acceptsGraphIso
    (fused (graph core2465) (root 10) 0 4) DegreeTwoThreeSpectrum4986.graph fusedMap2465=true := by decide +kernel
theorem certified2465 : Certified (graph core2465) (root 10) 0 4 :=
  of_native_maps core2465 DegreeTwoThreeSpectrum5359.graph DegreeTwoThreeSpectrum4986.graph
    sourceMap2465 fusedMap2465 sourceMap2465_checked fusedMap2465_checked
    DegreeTwoThreeFiniteComparisons.comparison2465
#print axioms sourceMap2465_checked
#print axioms fusedMap2465_checked
#print axioms certified2465
def sourceMap2465swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2465swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2465swap_checked : acceptsGraphIso
    (source (graph core2465) (root 10) 4 0) DegreeTwoThreeSpectrum5359.graph sourceMap2465swap=true := by decide +kernel
theorem fusedMap2465swap_checked : acceptsGraphIso
    (fused (graph core2465) (root 10) 4 0) DegreeTwoThreeSpectrum4986.graph fusedMap2465swap=true := by decide +kernel
theorem certified2465swap : Certified (graph core2465) (root 10) 4 0 :=
  of_native_maps core2465 DegreeTwoThreeSpectrum5359.graph DegreeTwoThreeSpectrum4986.graph
    sourceMap2465swap fusedMap2465swap sourceMap2465swap_checked fusedMap2465swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2465
#print axioms sourceMap2465swap_checked
#print axioms fusedMap2465swap_checked
#print axioms certified2465swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
