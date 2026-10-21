/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0765 : Family 8 := level8.get ⟨8,by decide⟩
def sourceMap0765 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0765 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0765_checked : acceptsGraphIso
    (source (graph core0765) (root 8) 0 2) DegreeOneSmallSpectrum868.graph sourceMap0765=true := by decide +kernel
theorem fusedMap0765_checked : acceptsGraphIso
    (fused (graph core0765) (root 8) 0 2) DegreeOneSmallSpectrum870.graph fusedMap0765=true := by decide +kernel
theorem certified0765 : Certified (graph core0765) (root 8) 0 2 :=
  of_native_maps core0765 DegreeOneSmallSpectrum868.graph DegreeOneSmallSpectrum870.graph
    sourceMap0765 fusedMap0765 sourceMap0765_checked fusedMap0765_checked
    DegreeOneSmallComparisons.comparison0765
#print axioms sourceMap0765_checked
#print axioms fusedMap0765_checked
#print axioms certified0765
def sourceMap0765swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0765swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0765swap_checked : acceptsGraphIso
    (source (graph core0765) (root 8) 2 0) DegreeOneSmallSpectrum868.graph sourceMap0765swap=true := by decide +kernel
theorem fusedMap0765swap_checked : acceptsGraphIso
    (fused (graph core0765) (root 8) 2 0) DegreeOneSmallSpectrum870.graph fusedMap0765swap=true := by decide +kernel
theorem certified0765swap : Certified (graph core0765) (root 8) 2 0 :=
  of_native_maps core0765 DegreeOneSmallSpectrum868.graph DegreeOneSmallSpectrum870.graph
    sourceMap0765swap fusedMap0765swap sourceMap0765swap_checked fusedMap0765swap_checked
    DegreeOneSmallComparisons.comparison0765
#print axioms sourceMap0765swap_checked
#print axioms fusedMap0765swap_checked
#print axioms certified0765swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
