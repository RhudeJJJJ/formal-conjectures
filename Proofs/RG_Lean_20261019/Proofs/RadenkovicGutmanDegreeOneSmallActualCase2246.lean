/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2246 : Family 10 := level10.get ⟨802,by decide⟩
def sourceMap2246 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,8,9,10,11,12,1,2,3,4,6,7] (sourceLabel 10 0 0 v)
def fusedMap2246 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,8,9,10,11,12,1,2,3,4,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2246_checked : acceptsGraphIso
    (source (graph core2246) (root 10) 0 0) DegreeOneSmallSpectrum1401.graph sourceMap2246=true := by decide +kernel
theorem fusedMap2246_checked : acceptsGraphIso
    (fused (graph core2246) (root 10) 0 0) DegreeOneSmallSpectrum1396.graph fusedMap2246=true := by decide +kernel
theorem certified2246 : Certified (graph core2246) (root 10) 0 0 :=
  of_native_maps core2246 DegreeOneSmallSpectrum1401.graph DegreeOneSmallSpectrum1396.graph
    sourceMap2246 fusedMap2246 sourceMap2246_checked fusedMap2246_checked
    DegreeOneSmallComparisons.comparison2246
#print axioms sourceMap2246_checked
#print axioms fusedMap2246_checked
#print axioms certified2246
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
