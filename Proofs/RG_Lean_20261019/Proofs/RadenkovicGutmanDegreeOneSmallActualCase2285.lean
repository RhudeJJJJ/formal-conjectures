/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2285 : Family 10 := level10.get ⟨896,by decide⟩
def sourceMap2285 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,8,9,10,11,12,1,2,3,4,6,7] (sourceLabel 10 0 0 v)
def fusedMap2285 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,8,9,10,11,12,1,2,3,4,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2285_checked : acceptsGraphIso
    (source (graph core2285) (root 10) 0 0) DegreeOneSmallSpectrum1194.graph sourceMap2285=true := by decide +kernel
theorem fusedMap2285_checked : acceptsGraphIso
    (fused (graph core2285) (root 10) 0 0) DegreeOneSmallSpectrum1188.graph fusedMap2285=true := by decide +kernel
theorem certified2285 : Certified (graph core2285) (root 10) 0 0 :=
  of_native_maps core2285 DegreeOneSmallSpectrum1194.graph DegreeOneSmallSpectrum1188.graph
    sourceMap2285 fusedMap2285 sourceMap2285_checked fusedMap2285_checked
    DegreeOneSmallComparisons.comparison2285
#print axioms sourceMap2285_checked
#print axioms fusedMap2285_checked
#print axioms certified2285
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
