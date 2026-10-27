/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3955 : Family 7 := level7.get ⟨24,by decide⟩
def sourceMap3955 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3955 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3955_checked : acceptsGraphIso
    (source (graph core3955) (root 7) 1 5) DegreeTwoThreeSpectrum4158.graph sourceMap3955=true := by decide +kernel
theorem fusedMap3955_checked : acceptsGraphIso
    (fused (graph core3955) (root 7) 1 5) DegreeTwoThreeSpectrum3883.graph fusedMap3955=true := by decide +kernel
theorem certified3955 : Certified (graph core3955) (root 7) 1 5 :=
  of_native_maps core3955 DegreeTwoThreeSpectrum4158.graph DegreeTwoThreeSpectrum3883.graph
    sourceMap3955 fusedMap3955 sourceMap3955_checked fusedMap3955_checked
    DegreeTwoThreeFiniteComparisons.comparison3955
#print axioms sourceMap3955_checked
#print axioms fusedMap3955_checked
#print axioms certified3955
def sourceMap3955swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,15,8,9] (sourceLabel 7 5 1 v)
def fusedMap3955swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3955swap_checked : acceptsGraphIso
    (source (graph core3955) (root 7) 5 1) DegreeTwoThreeSpectrum4158.graph sourceMap3955swap=true := by decide +kernel
theorem fusedMap3955swap_checked : acceptsGraphIso
    (fused (graph core3955) (root 7) 5 1) DegreeTwoThreeSpectrum3883.graph fusedMap3955swap=true := by decide +kernel
theorem certified3955swap : Certified (graph core3955) (root 7) 5 1 :=
  of_native_maps core3955 DegreeTwoThreeSpectrum4158.graph DegreeTwoThreeSpectrum3883.graph
    sourceMap3955swap fusedMap3955swap sourceMap3955swap_checked fusedMap3955swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3955
#print axioms sourceMap3955swap_checked
#print axioms fusedMap3955swap_checked
#print axioms certified3955swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
