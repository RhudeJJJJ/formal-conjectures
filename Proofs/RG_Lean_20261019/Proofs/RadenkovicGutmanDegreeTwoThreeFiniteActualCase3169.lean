/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3169 : Family 8 := level8.get ⟨106,by decide⟩
def sourceMap3169 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3169 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3169_checked : acceptsGraphIso
    (source (graph core3169) (root 8) 0 5) DegreeTwoThreeSpectrum4255.graph sourceMap3169=true := by decide +kernel
theorem fusedMap3169_checked : acceptsGraphIso
    (fused (graph core3169) (root 8) 0 5) DegreeTwoThreeSpectrum3908.graph fusedMap3169=true := by decide +kernel
theorem certified3169 : Certified (graph core3169) (root 8) 0 5 :=
  of_native_maps core3169 DegreeTwoThreeSpectrum4255.graph DegreeTwoThreeSpectrum3908.graph
    sourceMap3169 fusedMap3169 sourceMap3169_checked fusedMap3169_checked
    DegreeTwoThreeFiniteComparisons.comparison3169
#print axioms sourceMap3169_checked
#print axioms fusedMap3169_checked
#print axioms certified3169
def sourceMap3169swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3169swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3169swap_checked : acceptsGraphIso
    (source (graph core3169) (root 8) 5 0) DegreeTwoThreeSpectrum4255.graph sourceMap3169swap=true := by decide +kernel
theorem fusedMap3169swap_checked : acceptsGraphIso
    (fused (graph core3169) (root 8) 5 0) DegreeTwoThreeSpectrum3908.graph fusedMap3169swap=true := by decide +kernel
theorem certified3169swap : Certified (graph core3169) (root 8) 5 0 :=
  of_native_maps core3169 DegreeTwoThreeSpectrum4255.graph DegreeTwoThreeSpectrum3908.graph
    sourceMap3169swap fusedMap3169swap sourceMap3169swap_checked fusedMap3169swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3169
#print axioms sourceMap3169swap_checked
#print axioms fusedMap3169swap_checked
#print axioms certified3169swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
