/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2049 : Family 10 := level10.get ⟨412,by decide⟩
def sourceMap2049 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2049 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2049_checked : acceptsGraphIso
    (source (graph core2049) (root 10) 0 0) DegreeOneSmallSpectrum1123.graph sourceMap2049=true := by decide +kernel
theorem fusedMap2049_checked : acceptsGraphIso
    (fused (graph core2049) (root 10) 0 0) DegreeOneSmallSpectrum1499.graph fusedMap2049=true := by decide +kernel
theorem certified2049 : Certified (graph core2049) (root 10) 0 0 :=
  of_native_maps core2049 DegreeOneSmallSpectrum1123.graph DegreeOneSmallSpectrum1499.graph
    sourceMap2049 fusedMap2049 sourceMap2049_checked fusedMap2049_checked
    DegreeOneSmallComparisons.comparison2049
#print axioms sourceMap2049_checked
#print axioms fusedMap2049_checked
#print axioms certified2049
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
