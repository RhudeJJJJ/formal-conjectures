/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0465 : Family 7 := level7.get ⟨3,by decide⟩
def sourceMap0465 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,5,6,7,8,9,3,4] (sourceLabel 7 0 0 v)
def fusedMap0465 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,6,0,1,2,3,4,5,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0465_checked : acceptsGraphIso
    (source (graph core0465) (root 7) 0 0) DegreeOneSmallSpectrum079.graph sourceMap0465=true := by decide +kernel
theorem fusedMap0465_checked : acceptsGraphIso
    (fused (graph core0465) (root 7) 0 0) DegreeOneSmallSpectrum090.graph fusedMap0465=true := by decide +kernel
theorem certified0465 : Certified (graph core0465) (root 7) 0 0 :=
  of_native_maps core0465 DegreeOneSmallSpectrum079.graph DegreeOneSmallSpectrum090.graph
    sourceMap0465 fusedMap0465 sourceMap0465_checked fusedMap0465_checked
    DegreeOneSmallComparisons.comparison0465
#print axioms sourceMap0465_checked
#print axioms fusedMap0465_checked
#print axioms certified0465
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
