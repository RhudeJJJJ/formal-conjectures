/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons63
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3155 : Family 8 := level8.get ⟨67,by decide⟩
def sourceMap3155 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 8 0 5 v)
def fusedMap3155 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3155_checked : acceptsGraphIso
    (source (graph core3155) (root 8) 0 5) DegreeTwoThreeSpectrum4044.graph sourceMap3155=true := by decide +kernel
theorem fusedMap3155_checked : acceptsGraphIso
    (fused (graph core3155) (root 8) 0 5) DegreeTwoThreeSpectrum4045.graph fusedMap3155=true := by decide +kernel
theorem certified3155 : Certified (graph core3155) (root 8) 0 5 :=
  of_native_maps core3155 DegreeTwoThreeSpectrum4044.graph DegreeTwoThreeSpectrum4045.graph
    sourceMap3155 fusedMap3155 sourceMap3155_checked fusedMap3155_checked
    DegreeTwoThreeFiniteComparisons.comparison3155
#print axioms sourceMap3155_checked
#print axioms fusedMap3155_checked
#print axioms certified3155
def sourceMap3155swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,9] (sourceLabel 8 5 0 v)
def fusedMap3155swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3155swap_checked : acceptsGraphIso
    (source (graph core3155) (root 8) 5 0) DegreeTwoThreeSpectrum4044.graph sourceMap3155swap=true := by decide +kernel
theorem fusedMap3155swap_checked : acceptsGraphIso
    (fused (graph core3155) (root 8) 5 0) DegreeTwoThreeSpectrum4045.graph fusedMap3155swap=true := by decide +kernel
theorem certified3155swap : Certified (graph core3155) (root 8) 5 0 :=
  of_native_maps core3155 DegreeTwoThreeSpectrum4044.graph DegreeTwoThreeSpectrum4045.graph
    sourceMap3155swap fusedMap3155swap sourceMap3155swap_checked fusedMap3155swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3155
#print axioms sourceMap3155swap_checked
#print axioms fusedMap3155swap_checked
#print axioms certified3155swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
