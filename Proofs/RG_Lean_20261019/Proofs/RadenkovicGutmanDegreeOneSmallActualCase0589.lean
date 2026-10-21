/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0589 : Family 7 := level7.get ⟨31,by decide⟩
def sourceMap0589 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 1 1 v)
def fusedMap0589 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0589_checked : acceptsGraphIso
    (source (graph core0589) (root 7) 1 1) DegreeOneSmallSpectrum723.graph sourceMap0589=true := by decide +kernel
theorem fusedMap0589_checked : acceptsGraphIso
    (fused (graph core0589) (root 7) 1 1) DegreeOneSmallSpectrum440.graph fusedMap0589=true := by decide +kernel
theorem certified0589 : Certified (graph core0589) (root 7) 1 1 :=
  of_native_maps core0589 DegreeOneSmallSpectrum723.graph DegreeOneSmallSpectrum440.graph
    sourceMap0589 fusedMap0589 sourceMap0589_checked fusedMap0589_checked
    DegreeOneSmallComparisons.comparison0589
#print axioms sourceMap0589_checked
#print axioms fusedMap0589_checked
#print axioms certified0589
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
