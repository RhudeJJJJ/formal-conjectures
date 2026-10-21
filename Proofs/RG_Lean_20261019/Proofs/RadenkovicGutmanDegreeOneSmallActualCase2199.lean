/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2199 : Family 10 := level10.get ⟨708,by decide⟩
def sourceMap2199 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2199 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2199_checked : acceptsGraphIso
    (source (graph core2199) (root 10) 0 0) DegreeOneSmallSpectrum1764.graph sourceMap2199=true := by decide +kernel
theorem fusedMap2199_checked : acceptsGraphIso
    (fused (graph core2199) (root 10) 0 0) DegreeOneSmallSpectrum1328.graph fusedMap2199=true := by decide +kernel
theorem certified2199 : Certified (graph core2199) (root 10) 0 0 :=
  of_native_maps core2199 DegreeOneSmallSpectrum1764.graph DegreeOneSmallSpectrum1328.graph
    sourceMap2199 fusedMap2199 sourceMap2199_checked fusedMap2199_checked
    DegreeOneSmallComparisons.comparison2199
#print axioms sourceMap2199_checked
#print axioms fusedMap2199_checked
#print axioms certified2199
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
