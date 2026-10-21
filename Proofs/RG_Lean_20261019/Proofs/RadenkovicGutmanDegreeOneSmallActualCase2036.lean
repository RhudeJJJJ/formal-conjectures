/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2036 : Family 10 := level10.get ⟨392,by decide⟩
def sourceMap2036 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2036 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2036_checked : acceptsGraphIso
    (source (graph core2036) (root 10) 0 0) DegreeOneSmallSpectrum1178.graph sourceMap2036=true := by decide +kernel
theorem fusedMap2036_checked : acceptsGraphIso
    (fused (graph core2036) (root 10) 0 0) DegreeOneSmallSpectrum1496.graph fusedMap2036=true := by decide +kernel
theorem certified2036 : Certified (graph core2036) (root 10) 0 0 :=
  of_native_maps core2036 DegreeOneSmallSpectrum1178.graph DegreeOneSmallSpectrum1496.graph
    sourceMap2036 fusedMap2036 sourceMap2036_checked fusedMap2036_checked
    DegreeOneSmallComparisons.comparison2036
#print axioms sourceMap2036_checked
#print axioms fusedMap2036_checked
#print axioms certified2036
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
