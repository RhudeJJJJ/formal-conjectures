/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0032 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0032 : (Vertices 2 ⊕ Fin 1 ⊕ Fin 3) → Fin 7 :=
  fun v => ![0,1,2,3,4,5,6] (sourceLabel 2 0 2 v)
def fusedMap0032 : (Vertices 2 ⊕ Fin 4) → Fin 7 :=
  fun v => ![1,2,3,0,4,5,6] (fusedLabel 2 0 2 v)
theorem sourceMap0032_checked : acceptsGraphIso
    (source (graph core0032) (root 2) 0 2) DegreeOneSmallSpectrum009.graph sourceMap0032=true := by decide +kernel
theorem fusedMap0032_checked : acceptsGraphIso
    (fused (graph core0032) (root 2) 0 2) DegreeOneSmallSpectrum010.graph fusedMap0032=true := by decide +kernel
theorem certified0032 : Certified (graph core0032) (root 2) 0 2 :=
  of_native_maps core0032 DegreeOneSmallSpectrum009.graph DegreeOneSmallSpectrum010.graph
    sourceMap0032 fusedMap0032 sourceMap0032_checked fusedMap0032_checked
    DegreeOneSmallComparisons.comparison0032
#print axioms sourceMap0032_checked
#print axioms fusedMap0032_checked
#print axioms certified0032
def sourceMap0032swap : (Vertices 2 ⊕ Fin 3 ⊕ Fin 1) → Fin 7 :=
  fun v => ![0,1,2,4,5,6,3] (sourceLabel 2 2 0 v)
def fusedMap0032swap : (Vertices 2 ⊕ Fin 4) → Fin 7 :=
  fun v => ![1,2,3,0,4,5,6] (fusedLabel 2 2 0 v)
theorem sourceMap0032swap_checked : acceptsGraphIso
    (source (graph core0032) (root 2) 2 0) DegreeOneSmallSpectrum009.graph sourceMap0032swap=true := by decide +kernel
theorem fusedMap0032swap_checked : acceptsGraphIso
    (fused (graph core0032) (root 2) 2 0) DegreeOneSmallSpectrum010.graph fusedMap0032swap=true := by decide +kernel
theorem certified0032swap : Certified (graph core0032) (root 2) 2 0 :=
  of_native_maps core0032 DegreeOneSmallSpectrum009.graph DegreeOneSmallSpectrum010.graph
    sourceMap0032swap fusedMap0032swap sourceMap0032swap_checked fusedMap0032swap_checked
    DegreeOneSmallComparisons.comparison0032
#print axioms sourceMap0032swap_checked
#print axioms fusedMap0032swap_checked
#print axioms certified0032swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
