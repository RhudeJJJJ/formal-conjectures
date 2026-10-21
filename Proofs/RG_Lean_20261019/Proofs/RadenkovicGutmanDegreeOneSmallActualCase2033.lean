/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2033 : Family 10 := level10.get ⟨386,by decide⟩
def sourceMap2033 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2033 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2033_checked : acceptsGraphIso
    (source (graph core2033) (root 10) 0 0) DegreeOneSmallSpectrum1132.graph sourceMap2033=true := by decide +kernel
theorem fusedMap2033_checked : acceptsGraphIso
    (fused (graph core2033) (root 10) 0 0) DegreeOneSmallSpectrum1488.graph fusedMap2033=true := by decide +kernel
theorem certified2033 : Certified (graph core2033) (root 10) 0 0 :=
  of_native_maps core2033 DegreeOneSmallSpectrum1132.graph DegreeOneSmallSpectrum1488.graph
    sourceMap2033 fusedMap2033 sourceMap2033_checked fusedMap2033_checked
    DegreeOneSmallComparisons.comparison2033
#print axioms sourceMap2033_checked
#print axioms fusedMap2033_checked
#print axioms certified2033
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
