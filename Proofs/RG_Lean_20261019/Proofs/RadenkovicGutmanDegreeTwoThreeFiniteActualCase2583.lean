/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons51
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2583 : Family 10 := level10.get ⟨481,by decide⟩
def sourceMap2583 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2583 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 0 4 v)
theorem sourceMap2583_checked : acceptsGraphIso
    (source (graph core2583) (root 10) 0 4) DegreeTwoThreeSpectrum5944.graph sourceMap2583=true := by decide +kernel
theorem fusedMap2583_checked : acceptsGraphIso
    (fused (graph core2583) (root 10) 0 4) DegreeTwoThreeSpectrum5945.graph fusedMap2583=true := by decide +kernel
theorem certified2583 : Certified (graph core2583) (root 10) 0 4 :=
  of_native_maps core2583 DegreeTwoThreeSpectrum5944.graph DegreeTwoThreeSpectrum5945.graph
    sourceMap2583 fusedMap2583 sourceMap2583_checked fusedMap2583_checked
    DegreeTwoThreeFiniteComparisons.comparison2583
#print axioms sourceMap2583_checked
#print axioms fusedMap2583_checked
#print axioms certified2583
def sourceMap2583swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2583swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 4 0 v)
theorem sourceMap2583swap_checked : acceptsGraphIso
    (source (graph core2583) (root 10) 4 0) DegreeTwoThreeSpectrum5944.graph sourceMap2583swap=true := by decide +kernel
theorem fusedMap2583swap_checked : acceptsGraphIso
    (fused (graph core2583) (root 10) 4 0) DegreeTwoThreeSpectrum5945.graph fusedMap2583swap=true := by decide +kernel
theorem certified2583swap : Certified (graph core2583) (root 10) 4 0 :=
  of_native_maps core2583 DegreeTwoThreeSpectrum5944.graph DegreeTwoThreeSpectrum5945.graph
    sourceMap2583swap fusedMap2583swap sourceMap2583swap_checked fusedMap2583swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2583
#print axioms sourceMap2583swap_checked
#print axioms fusedMap2583swap_checked
#print axioms certified2583swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
