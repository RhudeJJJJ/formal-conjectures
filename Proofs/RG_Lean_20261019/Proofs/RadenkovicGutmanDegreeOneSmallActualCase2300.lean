/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2300 : Family 10 := level10.get ⟨935,by decide⟩
def sourceMap2300 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,0,9,10,11,12,1,2,3,7,8,5,6] (sourceLabel 10 0 0 v)
def fusedMap2300 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,4,5,6,7,8,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2300_checked : acceptsGraphIso
    (source (graph core2300) (root 10) 0 0) DegreeOneSmallSpectrum1468.graph sourceMap2300=true := by decide +kernel
theorem fusedMap2300_checked : acceptsGraphIso
    (fused (graph core2300) (root 10) 0 0) DegreeOneSmallSpectrum1456.graph fusedMap2300=true := by decide +kernel
theorem certified2300 : Certified (graph core2300) (root 10) 0 0 :=
  of_native_maps core2300 DegreeOneSmallSpectrum1468.graph DegreeOneSmallSpectrum1456.graph
    sourceMap2300 fusedMap2300 sourceMap2300_checked fusedMap2300_checked
    DegreeOneSmallComparisons.comparison2300
#print axioms sourceMap2300_checked
#print axioms fusedMap2300_checked
#print axioms certified2300
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
