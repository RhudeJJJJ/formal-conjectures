/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0846 : Family 8 := level8.get ⟨35,by decide⟩
def sourceMap0846 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap0846 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0846_checked : acceptsGraphIso
    (source (graph core0846) (root 8) 1 1) DegreeOneSmallSpectrum1031.graph sourceMap0846=true := by decide +kernel
theorem fusedMap0846_checked : acceptsGraphIso
    (fused (graph core0846) (root 8) 1 1) DegreeOneSmallSpectrum863.graph fusedMap0846=true := by decide +kernel
theorem certified0846 : Certified (graph core0846) (root 8) 1 1 :=
  of_native_maps core0846 DegreeOneSmallSpectrum1031.graph DegreeOneSmallSpectrum863.graph
    sourceMap0846 fusedMap0846 sourceMap0846_checked fusedMap0846_checked
    DegreeOneSmallComparisons.comparison0846
#print axioms sourceMap0846_checked
#print axioms fusedMap0846_checked
#print axioms certified0846
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
