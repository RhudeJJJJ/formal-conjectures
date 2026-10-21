/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2290 : Family 10 := level10.get ⟨903,by decide⟩
def sourceMap2290 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2290 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,4,5,6,7,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2290_checked : acceptsGraphIso
    (source (graph core2290) (root 10) 0 0) DegreeOneSmallSpectrum1733.graph sourceMap2290=true := by decide +kernel
theorem fusedMap2290_checked : acceptsGraphIso
    (fused (graph core2290) (root 10) 0 0) DegreeOneSmallSpectrum1477.graph fusedMap2290=true := by decide +kernel
theorem certified2290 : Certified (graph core2290) (root 10) 0 0 :=
  of_native_maps core2290 DegreeOneSmallSpectrum1733.graph DegreeOneSmallSpectrum1477.graph
    sourceMap2290 fusedMap2290 sourceMap2290_checked fusedMap2290_checked
    DegreeOneSmallComparisons.comparison2290
#print axioms sourceMap2290_checked
#print axioms fusedMap2290_checked
#print axioms certified2290
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
