/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3879 : Family 8 := level8.get ⟨168,by decide⟩
def sourceMap3879 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9,11,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3879 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3879_checked : acceptsGraphIso
    (source (graph core3879) (root 8) 1 4) DegreeTwoThreeSpectrum4581.graph sourceMap3879=true := by decide +kernel
theorem fusedMap3879_checked : acceptsGraphIso
    (fused (graph core3879) (root 8) 1 4) DegreeTwoThreeSpectrum4069.graph fusedMap3879=true := by decide +kernel
theorem certified3879 : Certified (graph core3879) (root 8) 1 4 :=
  of_native_maps core3879 DegreeTwoThreeSpectrum4581.graph DegreeTwoThreeSpectrum4069.graph
    sourceMap3879 fusedMap3879 sourceMap3879_checked fusedMap3879_checked
    DegreeTwoThreeFiniteComparisons.comparison3879
#print axioms sourceMap3879_checked
#print axioms fusedMap3879_checked
#print axioms certified3879
def sourceMap3879swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 8 4 1 v)
def fusedMap3879swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3879swap_checked : acceptsGraphIso
    (source (graph core3879) (root 8) 4 1) DegreeTwoThreeSpectrum4581.graph sourceMap3879swap=true := by decide +kernel
theorem fusedMap3879swap_checked : acceptsGraphIso
    (fused (graph core3879) (root 8) 4 1) DegreeTwoThreeSpectrum4069.graph fusedMap3879swap=true := by decide +kernel
theorem certified3879swap : Certified (graph core3879) (root 8) 4 1 :=
  of_native_maps core3879 DegreeTwoThreeSpectrum4581.graph DegreeTwoThreeSpectrum4069.graph
    sourceMap3879swap fusedMap3879swap sourceMap3879swap_checked fusedMap3879swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3879
#print axioms sourceMap3879swap_checked
#print axioms fusedMap3879swap_checked
#print axioms certified3879swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
