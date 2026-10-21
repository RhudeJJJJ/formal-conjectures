/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0314 : Family 6 := level6.get ⟨6,by decide⟩
def sourceMap0314 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap0314 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0314_checked : acceptsGraphIso
    (source (graph core0314) (root 6) 0 2) DegreeOneSmallSpectrum174.graph sourceMap0314=true := by decide +kernel
theorem fusedMap0314_checked : acceptsGraphIso
    (fused (graph core0314) (root 6) 0 2) DegreeOneSmallSpectrum175.graph fusedMap0314=true := by decide +kernel
theorem certified0314 : Certified (graph core0314) (root 6) 0 2 :=
  of_native_maps core0314 DegreeOneSmallSpectrum174.graph DegreeOneSmallSpectrum175.graph
    sourceMap0314 fusedMap0314 sourceMap0314_checked fusedMap0314_checked
    DegreeOneSmallComparisons.comparison0314
#print axioms sourceMap0314_checked
#print axioms fusedMap0314_checked
#print axioms certified0314
def sourceMap0314swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap0314swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0314swap_checked : acceptsGraphIso
    (source (graph core0314) (root 6) 2 0) DegreeOneSmallSpectrum174.graph sourceMap0314swap=true := by decide +kernel
theorem fusedMap0314swap_checked : acceptsGraphIso
    (fused (graph core0314) (root 6) 2 0) DegreeOneSmallSpectrum175.graph fusedMap0314swap=true := by decide +kernel
theorem certified0314swap : Certified (graph core0314) (root 6) 2 0 :=
  of_native_maps core0314 DegreeOneSmallSpectrum174.graph DegreeOneSmallSpectrum175.graph
    sourceMap0314swap fusedMap0314swap sourceMap0314swap_checked fusedMap0314swap_checked
    DegreeOneSmallComparisons.comparison0314
#print axioms sourceMap0314swap_checked
#print axioms fusedMap0314swap_checked
#print axioms certified0314swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
