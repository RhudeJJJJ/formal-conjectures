/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons77
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3851 : Family 8 := level8.get ⟨91,by decide⟩
def sourceMap3851 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,11,12,13,14,15,6,7,8,9,10] (sourceLabel 8 1 4 v)
def fusedMap3851 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3851_checked : acceptsGraphIso
    (source (graph core3851) (root 8) 1 4) DegreeTwoThreeSpectrum4661.graph sourceMap3851=true := by decide +kernel
theorem fusedMap3851_checked : acceptsGraphIso
    (fused (graph core3851) (root 8) 1 4) DegreeTwoThreeSpectrum4154.graph fusedMap3851=true := by decide +kernel
theorem certified3851 : Certified (graph core3851) (root 8) 1 4 :=
  of_native_maps core3851 DegreeTwoThreeSpectrum4661.graph DegreeTwoThreeSpectrum4154.graph
    sourceMap3851 fusedMap3851 sourceMap3851_checked fusedMap3851_checked
    DegreeTwoThreeFiniteComparisons.comparison3851
#print axioms sourceMap3851_checked
#print axioms fusedMap3851_checked
#print axioms certified3851
def sourceMap3851swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,11,12,13,6,7,8,9,10,14,15] (sourceLabel 8 4 1 v)
def fusedMap3851swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3851swap_checked : acceptsGraphIso
    (source (graph core3851) (root 8) 4 1) DegreeTwoThreeSpectrum4661.graph sourceMap3851swap=true := by decide +kernel
theorem fusedMap3851swap_checked : acceptsGraphIso
    (fused (graph core3851) (root 8) 4 1) DegreeTwoThreeSpectrum4154.graph fusedMap3851swap=true := by decide +kernel
theorem certified3851swap : Certified (graph core3851) (root 8) 4 1 :=
  of_native_maps core3851 DegreeTwoThreeSpectrum4661.graph DegreeTwoThreeSpectrum4154.graph
    sourceMap3851swap fusedMap3851swap sourceMap3851swap_checked fusedMap3851swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3851
#print axioms sourceMap3851swap_checked
#print axioms fusedMap3851swap_checked
#print axioms certified3851swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
