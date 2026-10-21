/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0353 : Family 6 := level6.get ⟨11,by decide⟩
def sourceMap0353 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (sourceLabel 6 1 1 v)
def fusedMap0353 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0353_checked : acceptsGraphIso
    (source (graph core0353) (root 6) 1 1) DegreeOneSmallSpectrum327.graph sourceMap0353=true := by decide +kernel
theorem fusedMap0353_checked : acceptsGraphIso
    (fused (graph core0353) (root 6) 1 1) DegreeOneSmallSpectrum207.graph fusedMap0353=true := by decide +kernel
theorem certified0353 : Certified (graph core0353) (root 6) 1 1 :=
  of_native_maps core0353 DegreeOneSmallSpectrum327.graph DegreeOneSmallSpectrum207.graph
    sourceMap0353 fusedMap0353 sourceMap0353_checked fusedMap0353_checked
    DegreeOneSmallComparisons.comparison0353
#print axioms sourceMap0353_checked
#print axioms fusedMap0353_checked
#print axioms certified0353
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
