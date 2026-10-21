/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2271 : Family 10 := level10.get ⟨859,by decide⟩
def sourceMap2271 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2271 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2271_checked : acceptsGraphIso
    (source (graph core2271) (root 10) 0 0) DegreeOneSmallSpectrum1809.graph sourceMap2271=true := by decide +kernel
theorem fusedMap2271_checked : acceptsGraphIso
    (fused (graph core2271) (root 10) 0 0) DegreeOneSmallSpectrum1483.graph fusedMap2271=true := by decide +kernel
theorem certified2271 : Certified (graph core2271) (root 10) 0 0 :=
  of_native_maps core2271 DegreeOneSmallSpectrum1809.graph DegreeOneSmallSpectrum1483.graph
    sourceMap2271 fusedMap2271 sourceMap2271_checked fusedMap2271_checked
    DegreeOneSmallComparisons.comparison2271
#print axioms sourceMap2271_checked
#print axioms fusedMap2271_checked
#print axioms certified2271
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
