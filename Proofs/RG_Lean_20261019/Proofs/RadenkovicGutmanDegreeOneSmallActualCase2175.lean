/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2175 : Family 10 := level10.get ⟨655,by decide⟩
def sourceMap2175 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,5,0,1,2,3,4,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2175 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,5,0,1,2,3,4,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2175_checked : acceptsGraphIso
    (source (graph core2175) (root 10) 0 0) DegreeOneSmallSpectrum1266.graph sourceMap2175=true := by decide +kernel
theorem fusedMap2175_checked : acceptsGraphIso
    (fused (graph core2175) (root 10) 0 0) DegreeOneSmallSpectrum1265.graph fusedMap2175=true := by decide +kernel
theorem certified2175 : Certified (graph core2175) (root 10) 0 0 :=
  of_native_maps core2175 DegreeOneSmallSpectrum1266.graph DegreeOneSmallSpectrum1265.graph
    sourceMap2175 fusedMap2175 sourceMap2175_checked fusedMap2175_checked
    DegreeOneSmallComparisons.comparison2175
#print axioms sourceMap2175_checked
#print axioms fusedMap2175_checked
#print axioms certified2175
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
