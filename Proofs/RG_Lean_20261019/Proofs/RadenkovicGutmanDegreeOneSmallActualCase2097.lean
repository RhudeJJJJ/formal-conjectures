/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2097 : Family 10 := level10.get ⟨516,by decide⟩
def sourceMap2097 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2097 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2097_checked : acceptsGraphIso
    (source (graph core2097) (root 10) 0 0) DegreeOneSmallSpectrum1612.graph sourceMap2097=true := by decide +kernel
theorem fusedMap2097_checked : acceptsGraphIso
    (fused (graph core2097) (root 10) 0 0) DegreeOneSmallSpectrum1009.graph fusedMap2097=true := by decide +kernel
theorem certified2097 : Certified (graph core2097) (root 10) 0 0 :=
  of_native_maps core2097 DegreeOneSmallSpectrum1612.graph DegreeOneSmallSpectrum1009.graph
    sourceMap2097 fusedMap2097 sourceMap2097_checked fusedMap2097_checked
    DegreeOneSmallComparisons.comparison2097
#print axioms sourceMap2097_checked
#print axioms fusedMap2097_checked
#print axioms certified2097
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
