/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2460 : Family 10 := level10.get ⟨1531,by decide⟩
def sourceMap2460 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2460 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2460_checked : acceptsGraphIso
    (source (graph core2460) (root 10) 0 0) DegreeOneSmallSpectrum1995.graph sourceMap2460=true := by decide +kernel
theorem fusedMap2460_checked : acceptsGraphIso
    (fused (graph core2460) (root 10) 0 0) DegreeOneSmallSpectrum1532.graph fusedMap2460=true := by decide +kernel
theorem certified2460 : Certified (graph core2460) (root 10) 0 0 :=
  of_native_maps core2460 DegreeOneSmallSpectrum1995.graph DegreeOneSmallSpectrum1532.graph
    sourceMap2460 fusedMap2460 sourceMap2460_checked fusedMap2460_checked
    DegreeOneSmallComparisons.comparison2460
#print axioms sourceMap2460_checked
#print axioms fusedMap2460_checked
#print axioms certified2460
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
