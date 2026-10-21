/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0026 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0026 : (Vertices 1 ⊕ Fin 4 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,6,2,3,4,5,0,7,8,9,10,11] (sourceLabel 1 3 5 v)
def fusedMap0026 : (Vertices 1 ⊕ Fin 10) → Fin 12 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10,11] (fusedLabel 1 3 5 v)
theorem sourceMap0026_checked : acceptsGraphIso
    (source (graph core0026) (root 1) 3 5) DegreeOneSmallSpectrum396.graph sourceMap0026=true := by decide +kernel
theorem fusedMap0026_checked : acceptsGraphIso
    (fused (graph core0026) (root 1) 3 5) DegreeOneSmallSpectrum369.graph fusedMap0026=true := by decide +kernel
theorem certified0026 : Certified (graph core0026) (root 1) 3 5 :=
  of_native_maps core0026 DegreeOneSmallSpectrum396.graph DegreeOneSmallSpectrum369.graph
    sourceMap0026 fusedMap0026 sourceMap0026_checked fusedMap0026_checked
    DegreeOneSmallComparisons.comparison0026
#print axioms sourceMap0026_checked
#print axioms fusedMap0026_checked
#print axioms certified0026
def sourceMap0026swap : (Vertices 1 ⊕ Fin 6 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,6,0,7,8,9,10,11,2,3,4,5] (sourceLabel 1 5 3 v)
def fusedMap0026swap : (Vertices 1 ⊕ Fin 10) → Fin 12 :=
  fun v => ![4,5,3,2,1,0,6,7,8,9,10,11] (fusedLabel 1 5 3 v)
theorem sourceMap0026swap_checked : acceptsGraphIso
    (source (graph core0026) (root 1) 5 3) DegreeOneSmallSpectrum396.graph sourceMap0026swap=true := by decide +kernel
theorem fusedMap0026swap_checked : acceptsGraphIso
    (fused (graph core0026) (root 1) 5 3) DegreeOneSmallSpectrum369.graph fusedMap0026swap=true := by decide +kernel
theorem certified0026swap : Certified (graph core0026) (root 1) 5 3 :=
  of_native_maps core0026 DegreeOneSmallSpectrum396.graph DegreeOneSmallSpectrum369.graph
    sourceMap0026swap fusedMap0026swap sourceMap0026swap_checked fusedMap0026swap_checked
    DegreeOneSmallComparisons.comparison0026
#print axioms sourceMap0026swap_checked
#print axioms fusedMap0026swap_checked
#print axioms certified0026swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
