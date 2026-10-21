/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2337 : Family 10 := level10.get ⟨1046,by decide⟩
def sourceMap2337 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2337 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2337_checked : acceptsGraphIso
    (source (graph core2337) (root 10) 0 0) DegreeOneSmallSpectrum1642.graph sourceMap2337=true := by decide +kernel
theorem fusedMap2337_checked : acceptsGraphIso
    (fused (graph core2337) (root 10) 0 0) DegreeOneSmallSpectrum1646.graph fusedMap2337=true := by decide +kernel
theorem certified2337 : Certified (graph core2337) (root 10) 0 0 :=
  of_native_maps core2337 DegreeOneSmallSpectrum1642.graph DegreeOneSmallSpectrum1646.graph
    sourceMap2337 fusedMap2337 sourceMap2337_checked fusedMap2337_checked
    DegreeOneSmallComparisons.comparison2337
#print axioms sourceMap2337_checked
#print axioms fusedMap2337_checked
#print axioms certified2337
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
