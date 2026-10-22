/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons64
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3212 : Family 8 := level8.get ⟨212,by decide⟩
def sourceMap3212 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3212 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3212_checked : acceptsGraphIso
    (source (graph core3212) (root 8) 0 5) DegreeTwoThreeSpectrum4277.graph sourceMap3212=true := by decide +kernel
theorem fusedMap3212_checked : acceptsGraphIso
    (fused (graph core3212) (root 8) 0 5) DegreeTwoThreeSpectrum4278.graph fusedMap3212=true := by decide +kernel
theorem certified3212 : Certified (graph core3212) (root 8) 0 5 :=
  of_native_maps core3212 DegreeTwoThreeSpectrum4277.graph DegreeTwoThreeSpectrum4278.graph
    sourceMap3212 fusedMap3212 sourceMap3212_checked fusedMap3212_checked
    DegreeTwoThreeFiniteComparisons.comparison3212
#print axioms sourceMap3212_checked
#print axioms fusedMap3212_checked
#print axioms certified3212
def sourceMap3212swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,10] (sourceLabel 8 5 0 v)
def fusedMap3212swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3212swap_checked : acceptsGraphIso
    (source (graph core3212) (root 8) 5 0) DegreeTwoThreeSpectrum4277.graph sourceMap3212swap=true := by decide +kernel
theorem fusedMap3212swap_checked : acceptsGraphIso
    (fused (graph core3212) (root 8) 5 0) DegreeTwoThreeSpectrum4278.graph fusedMap3212swap=true := by decide +kernel
theorem certified3212swap : Certified (graph core3212) (root 8) 5 0 :=
  of_native_maps core3212 DegreeTwoThreeSpectrum4277.graph DegreeTwoThreeSpectrum4278.graph
    sourceMap3212swap fusedMap3212swap sourceMap3212swap_checked fusedMap3212swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3212
#print axioms sourceMap3212swap_checked
#print axioms fusedMap3212swap_checked
#print axioms certified3212swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
