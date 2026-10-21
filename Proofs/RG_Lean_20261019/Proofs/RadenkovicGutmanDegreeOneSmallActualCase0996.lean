/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0996 : Family 8 := level8.get ⟨99,by decide⟩
def sourceMap0996 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (sourceLabel 8 0 1 v)
def fusedMap0996 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0996_checked : acceptsGraphIso
    (source (graph core0996) (root 8) 0 1) DegreeOneSmallSpectrum639.graph sourceMap0996=true := by decide +kernel
theorem fusedMap0996_checked : acceptsGraphIso
    (fused (graph core0996) (root 8) 0 1) DegreeOneSmallSpectrum405.graph fusedMap0996=true := by decide +kernel
theorem certified0996 : Certified (graph core0996) (root 8) 0 1 :=
  of_native_maps core0996 DegreeOneSmallSpectrum639.graph DegreeOneSmallSpectrum405.graph
    sourceMap0996 fusedMap0996 sourceMap0996_checked fusedMap0996_checked
    DegreeOneSmallComparisons.comparison0996
#print axioms sourceMap0996_checked
#print axioms fusedMap0996_checked
#print axioms certified0996
def sourceMap0996swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 8 1 0 v)
def fusedMap0996swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0996swap_checked : acceptsGraphIso
    (source (graph core0996) (root 8) 1 0) DegreeOneSmallSpectrum639.graph sourceMap0996swap=true := by decide +kernel
theorem fusedMap0996swap_checked : acceptsGraphIso
    (fused (graph core0996) (root 8) 1 0) DegreeOneSmallSpectrum405.graph fusedMap0996swap=true := by decide +kernel
theorem certified0996swap : Certified (graph core0996) (root 8) 1 0 :=
  of_native_maps core0996 DegreeOneSmallSpectrum639.graph DegreeOneSmallSpectrum405.graph
    sourceMap0996swap fusedMap0996swap sourceMap0996swap_checked fusedMap0996swap_checked
    DegreeOneSmallComparisons.comparison0996
#print axioms sourceMap0996swap_checked
#print axioms fusedMap0996swap_checked
#print axioms certified0996swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
