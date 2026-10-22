/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3180 : Family 8 := level8.get ⟨138,by decide⟩
def sourceMap3180 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3180 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3180_checked : acceptsGraphIso
    (source (graph core3180) (root 8) 0 5) DegreeTwoThreeSpectrum4428.graph sourceMap3180=true := by decide +kernel
theorem fusedMap3180_checked : acceptsGraphIso
    (fused (graph core3180) (root 8) 0 5) DegreeTwoThreeSpectrum3989.graph fusedMap3180=true := by decide +kernel
theorem certified3180 : Certified (graph core3180) (root 8) 0 5 :=
  of_native_maps core3180 DegreeTwoThreeSpectrum4428.graph DegreeTwoThreeSpectrum3989.graph
    sourceMap3180 fusedMap3180 sourceMap3180_checked fusedMap3180_checked
    DegreeTwoThreeFiniteComparisons.comparison3180
#print axioms sourceMap3180_checked
#print axioms fusedMap3180_checked
#print axioms certified3180
def sourceMap3180swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3180swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3180swap_checked : acceptsGraphIso
    (source (graph core3180) (root 8) 5 0) DegreeTwoThreeSpectrum4428.graph sourceMap3180swap=true := by decide +kernel
theorem fusedMap3180swap_checked : acceptsGraphIso
    (fused (graph core3180) (root 8) 5 0) DegreeTwoThreeSpectrum3989.graph fusedMap3180swap=true := by decide +kernel
theorem certified3180swap : Certified (graph core3180) (root 8) 5 0 :=
  of_native_maps core3180 DegreeTwoThreeSpectrum4428.graph DegreeTwoThreeSpectrum3989.graph
    sourceMap3180swap fusedMap3180swap sourceMap3180swap_checked fusedMap3180swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3180
#print axioms sourceMap3180swap_checked
#print axioms fusedMap3180swap_checked
#print axioms certified3180swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
