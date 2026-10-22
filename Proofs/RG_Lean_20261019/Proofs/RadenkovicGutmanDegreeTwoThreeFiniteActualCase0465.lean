/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0465 : Family 10 := level10.get ⟨278,by decide⟩
def sourceMap0465 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0465 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0465_checked : acceptsGraphIso
    (source (graph core0465) (root 10) 0 0) DegreeOneSmallSpectrum1263.graph sourceMap0465=true := by decide +kernel
theorem fusedMap0465_checked : acceptsGraphIso
    (fused (graph core0465) (root 10) 0 0) DegreeOneSmallSpectrum1256.graph fusedMap0465=true := by decide +kernel
theorem certified0465 : Certified (graph core0465) (root 10) 0 0 :=
  of_native_maps core0465 DegreeOneSmallSpectrum1263.graph DegreeOneSmallSpectrum1256.graph
    sourceMap0465 fusedMap0465 sourceMap0465_checked fusedMap0465_checked
    DegreeTwoThreeFiniteComparisons.comparison0465
#print axioms sourceMap0465_checked
#print axioms fusedMap0465_checked
#print axioms certified0465
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
