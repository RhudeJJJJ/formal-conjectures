/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3528 : Family 7 := level7.get ⟨78,by decide⟩
def sourceMap3528 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3528 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3528_checked : acceptsGraphIso
    (source (graph core3528) (root 7) 0 6) DegreeTwoThreeSpectrum4343.graph sourceMap3528=true := by decide +kernel
theorem fusedMap3528_checked : acceptsGraphIso
    (fused (graph core3528) (root 7) 0 6) DegreeTwoThreeSpectrum3942.graph fusedMap3528=true := by decide +kernel
theorem certified3528 : Certified (graph core3528) (root 7) 0 6 :=
  of_native_maps core3528 DegreeTwoThreeSpectrum4343.graph DegreeTwoThreeSpectrum3942.graph
    sourceMap3528 fusedMap3528 sourceMap3528_checked fusedMap3528_checked
    DegreeTwoThreeFiniteComparisons.comparison3528
#print axioms sourceMap3528_checked
#print axioms fusedMap3528_checked
#print axioms certified3528
def sourceMap3528swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3528swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3528swap_checked : acceptsGraphIso
    (source (graph core3528) (root 7) 6 0) DegreeTwoThreeSpectrum4343.graph sourceMap3528swap=true := by decide +kernel
theorem fusedMap3528swap_checked : acceptsGraphIso
    (fused (graph core3528) (root 7) 6 0) DegreeTwoThreeSpectrum3942.graph fusedMap3528swap=true := by decide +kernel
theorem certified3528swap : Certified (graph core3528) (root 7) 6 0 :=
  of_native_maps core3528 DegreeTwoThreeSpectrum4343.graph DegreeTwoThreeSpectrum3942.graph
    sourceMap3528swap fusedMap3528swap sourceMap3528swap_checked fusedMap3528swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3528
#print axioms sourceMap3528swap_checked
#print axioms fusedMap3528swap_checked
#print axioms certified3528swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
