/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0361 : Family 6 := level6.get ⟨12,by decide⟩
def sourceMap0361 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 0 4 v)
def fusedMap0361 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 0 4 v)
theorem sourceMap0361_checked : acceptsGraphIso
    (source (graph core0361) (root 6) 0 4) DegreeOneSmallSpectrum925.graph sourceMap0361=true := by decide +kernel
theorem fusedMap0361_checked : acceptsGraphIso
    (fused (graph core0361) (root 6) 0 4) DegreeOneSmallSpectrum929.graph fusedMap0361=true := by decide +kernel
theorem certified0361 : Certified (graph core0361) (root 6) 0 4 :=
  of_native_maps core0361 DegreeOneSmallSpectrum925.graph DegreeOneSmallSpectrum929.graph
    sourceMap0361 fusedMap0361 sourceMap0361_checked fusedMap0361_checked
    DegreeOneSmallComparisons.comparison0361
#print axioms sourceMap0361_checked
#print axioms fusedMap0361_checked
#print axioms certified0361
def sourceMap0361swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,8,9,10,11,12,7] (sourceLabel 6 4 0 v)
def fusedMap0361swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 4 0 v)
theorem sourceMap0361swap_checked : acceptsGraphIso
    (source (graph core0361) (root 6) 4 0) DegreeOneSmallSpectrum925.graph sourceMap0361swap=true := by decide +kernel
theorem fusedMap0361swap_checked : acceptsGraphIso
    (fused (graph core0361) (root 6) 4 0) DegreeOneSmallSpectrum929.graph fusedMap0361swap=true := by decide +kernel
theorem certified0361swap : Certified (graph core0361) (root 6) 4 0 :=
  of_native_maps core0361 DegreeOneSmallSpectrum925.graph DegreeOneSmallSpectrum929.graph
    sourceMap0361swap fusedMap0361swap sourceMap0361swap_checked fusedMap0361swap_checked
    DegreeOneSmallComparisons.comparison0361
#print axioms sourceMap0361swap_checked
#print axioms fusedMap0361swap_checked
#print axioms certified0361swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
