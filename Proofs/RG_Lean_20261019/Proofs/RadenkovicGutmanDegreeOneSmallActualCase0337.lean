/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0337 : Family 6 := level6.get ⟨8,by decide⟩
def sourceMap0337 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,11,12,7,8,9,10] (sourceLabel 6 1 3 v)
def fusedMap0337 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0337_checked : acceptsGraphIso
    (source (graph core0337) (root 6) 1 3) DegreeOneSmallSpectrum1246.graph sourceMap0337=true := by decide +kernel
theorem fusedMap0337_checked : acceptsGraphIso
    (fused (graph core0337) (root 6) 1 3) DegreeOneSmallSpectrum887.graph fusedMap0337=true := by decide +kernel
theorem certified0337 : Certified (graph core0337) (root 6) 1 3 :=
  of_native_maps core0337 DegreeOneSmallSpectrum1246.graph DegreeOneSmallSpectrum887.graph
    sourceMap0337 fusedMap0337 sourceMap0337_checked fusedMap0337_checked
    DegreeOneSmallComparisons.comparison0337
#print axioms sourceMap0337_checked
#print axioms fusedMap0337_checked
#print axioms certified0337
def sourceMap0337swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 3 1 v)
def fusedMap0337swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0337swap_checked : acceptsGraphIso
    (source (graph core0337) (root 6) 3 1) DegreeOneSmallSpectrum1246.graph sourceMap0337swap=true := by decide +kernel
theorem fusedMap0337swap_checked : acceptsGraphIso
    (fused (graph core0337) (root 6) 3 1) DegreeOneSmallSpectrum887.graph fusedMap0337swap=true := by decide +kernel
theorem certified0337swap : Certified (graph core0337) (root 6) 3 1 :=
  of_native_maps core0337 DegreeOneSmallSpectrum1246.graph DegreeOneSmallSpectrum887.graph
    sourceMap0337swap fusedMap0337swap sourceMap0337swap_checked fusedMap0337swap_checked
    DegreeOneSmallComparisons.comparison0337
#print axioms sourceMap0337swap_checked
#print axioms fusedMap0337swap_checked
#print axioms certified0337swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
