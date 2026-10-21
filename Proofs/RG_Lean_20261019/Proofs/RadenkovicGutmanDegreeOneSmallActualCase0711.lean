/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0711 : Family 7 := level7.get ⟨81,by decide⟩
def sourceMap0711 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,4,5,6,7,8,9,2,3] (sourceLabel 7 0 0 v)
def fusedMap0711 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0711_checked : acceptsGraphIso
    (source (graph core0711) (root 7) 0 0) DegreeOneSmallSpectrum161.graph sourceMap0711=true := by decide +kernel
theorem fusedMap0711_checked : acceptsGraphIso
    (fused (graph core0711) (root 7) 0 0) DegreeOneSmallSpectrum130.graph fusedMap0711=true := by decide +kernel
theorem certified0711 : Certified (graph core0711) (root 7) 0 0 :=
  of_native_maps core0711 DegreeOneSmallSpectrum161.graph DegreeOneSmallSpectrum130.graph
    sourceMap0711 fusedMap0711 sourceMap0711_checked fusedMap0711_checked
    DegreeOneSmallComparisons.comparison0711
#print axioms sourceMap0711_checked
#print axioms fusedMap0711_checked
#print axioms certified0711
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
