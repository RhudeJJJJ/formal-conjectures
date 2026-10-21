/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0017 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0017 : (Vertices 1 ⊕ Fin 2 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,6,4,5,2,1,0,7,8,9,10,11,12] (sourceLabel 1 1 8 v)
def fusedMap0017 : (Vertices 1 ⊕ Fin 11) → Fin 13 :=
  fun v => ![5,6,4,3,2,1,0,7,8,9,10,11,12] (fusedLabel 1 1 8 v)
theorem sourceMap0017_checked : acceptsGraphIso
    (source (graph core0017) (root 1) 1 8) DegreeOneSmallSpectrum857.graph sourceMap0017=true := by decide +kernel
theorem fusedMap0017_checked : acceptsGraphIso
    (fused (graph core0017) (root 1) 1 8) DegreeOneSmallSpectrum861.graph fusedMap0017=true := by decide +kernel
theorem certified0017 : Certified (graph core0017) (root 1) 1 8 :=
  of_native_maps core0017 DegreeOneSmallSpectrum857.graph DegreeOneSmallSpectrum861.graph
    sourceMap0017 fusedMap0017 sourceMap0017_checked fusedMap0017_checked
    DegreeOneSmallComparisons.comparison0017
#print axioms sourceMap0017_checked
#print axioms fusedMap0017_checked
#print axioms certified0017
def sourceMap0017swap : (Vertices 1 ⊕ Fin 9 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,6,2,1,0,7,8,9,10,11,12,4,5] (sourceLabel 1 8 1 v)
def fusedMap0017swap : (Vertices 1 ⊕ Fin 11) → Fin 13 :=
  fun v => ![5,6,4,3,2,1,0,7,8,9,10,11,12] (fusedLabel 1 8 1 v)
theorem sourceMap0017swap_checked : acceptsGraphIso
    (source (graph core0017) (root 1) 8 1) DegreeOneSmallSpectrum857.graph sourceMap0017swap=true := by decide +kernel
theorem fusedMap0017swap_checked : acceptsGraphIso
    (fused (graph core0017) (root 1) 8 1) DegreeOneSmallSpectrum861.graph fusedMap0017swap=true := by decide +kernel
theorem certified0017swap : Certified (graph core0017) (root 1) 8 1 :=
  of_native_maps core0017 DegreeOneSmallSpectrum857.graph DegreeOneSmallSpectrum861.graph
    sourceMap0017swap fusedMap0017swap sourceMap0017swap_checked fusedMap0017swap_checked
    DegreeOneSmallComparisons.comparison0017
#print axioms sourceMap0017swap_checked
#print axioms fusedMap0017swap_checked
#print axioms certified0017swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
