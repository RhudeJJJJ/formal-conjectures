/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2287 : Family 10 := level10.get ⟨898,by decide⟩
def sourceMap2287 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,0,8,9,10,11,12,1,2,3,7,5,6] (sourceLabel 10 0 0 v)
def fusedMap2287 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,4,5,6,7,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2287_checked : acceptsGraphIso
    (source (graph core2287) (root 10) 0 0) DegreeOneSmallSpectrum1470.graph sourceMap2287=true := by decide +kernel
theorem fusedMap2287_checked : acceptsGraphIso
    (fused (graph core2287) (root 10) 0 0) DegreeOneSmallSpectrum1458.graph fusedMap2287=true := by decide +kernel
theorem certified2287 : Certified (graph core2287) (root 10) 0 0 :=
  of_native_maps core2287 DegreeOneSmallSpectrum1470.graph DegreeOneSmallSpectrum1458.graph
    sourceMap2287 fusedMap2287 sourceMap2287_checked fusedMap2287_checked
    DegreeOneSmallComparisons.comparison2287
#print axioms sourceMap2287_checked
#print axioms fusedMap2287_checked
#print axioms certified2287
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
