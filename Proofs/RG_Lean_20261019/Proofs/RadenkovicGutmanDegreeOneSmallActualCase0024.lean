/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0024 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0024 : (Vertices 1 ⊕ Fin 4 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,9,1,2,3,4,5,6,7,8] (sourceLabel 1 3 3 v)
def fusedMap0024 : (Vertices 1 ⊕ Fin 8) → Fin 10 :=
  fun v => ![3,4,2,1,0,5,6,7,8,9] (fusedLabel 1 3 3 v)
theorem sourceMap0024_checked : acceptsGraphIso
    (source (graph core0024) (root 1) 3 3) DegreeOneSmallSpectrum091.graph sourceMap0024=true := by decide +kernel
theorem fusedMap0024_checked : acceptsGraphIso
    (fused (graph core0024) (root 1) 3 3) DegreeOneSmallSpectrum073.graph fusedMap0024=true := by decide +kernel
theorem certified0024 : Certified (graph core0024) (root 1) 3 3 :=
  of_native_maps core0024 DegreeOneSmallSpectrum091.graph DegreeOneSmallSpectrum073.graph
    sourceMap0024 fusedMap0024 sourceMap0024_checked fusedMap0024_checked
    DegreeOneSmallComparisons.comparison0024
#print axioms sourceMap0024_checked
#print axioms fusedMap0024_checked
#print axioms certified0024
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
