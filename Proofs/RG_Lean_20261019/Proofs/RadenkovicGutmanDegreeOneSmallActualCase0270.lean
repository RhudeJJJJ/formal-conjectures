/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0270 : Family 6 := level6.get ⟨0,by decide⟩
def sourceMap0270 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,6,2,3,4,5] (sourceLabel 6 0 3 v)
def fusedMap0270 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (fusedLabel 6 0 3 v)
theorem sourceMap0270_checked : acceptsGraphIso
    (source (graph core0270) (root 6) 0 3) DegreeOneSmallSpectrum396.graph sourceMap0270=true := by decide +kernel
theorem fusedMap0270_checked : acceptsGraphIso
    (fused (graph core0270) (root 6) 0 3) DegreeOneSmallSpectrum369.graph fusedMap0270=true := by decide +kernel
theorem certified0270 : Certified (graph core0270) (root 6) 0 3 :=
  of_native_maps core0270 DegreeOneSmallSpectrum396.graph DegreeOneSmallSpectrum369.graph
    sourceMap0270 fusedMap0270 sourceMap0270_checked fusedMap0270_checked
    DegreeOneSmallComparisons.comparison0270
#print axioms sourceMap0270_checked
#print axioms fusedMap0270_checked
#print axioms certified0270
def sourceMap0270swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,2,3,4,5,6] (sourceLabel 6 3 0 v)
def fusedMap0270swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (fusedLabel 6 3 0 v)
theorem sourceMap0270swap_checked : acceptsGraphIso
    (source (graph core0270) (root 6) 3 0) DegreeOneSmallSpectrum396.graph sourceMap0270swap=true := by decide +kernel
theorem fusedMap0270swap_checked : acceptsGraphIso
    (fused (graph core0270) (root 6) 3 0) DegreeOneSmallSpectrum369.graph fusedMap0270swap=true := by decide +kernel
theorem certified0270swap : Certified (graph core0270) (root 6) 3 0 :=
  of_native_maps core0270 DegreeOneSmallSpectrum396.graph DegreeOneSmallSpectrum369.graph
    sourceMap0270swap fusedMap0270swap sourceMap0270swap_checked fusedMap0270swap_checked
    DegreeOneSmallComparisons.comparison0270
#print axioms sourceMap0270swap_checked
#print axioms fusedMap0270swap_checked
#print axioms certified0270swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
