/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2470 : Family 10 := level10.get ⟨1569,by decide⟩
def sourceMap2470 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (sourceLabel 10 0 0 v)
def fusedMap2470 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2470_checked : acceptsGraphIso
    (source (graph core2470) (root 10) 0 0) DegreeOneSmallSpectrum2005.graph sourceMap2470=true := by decide +kernel
theorem fusedMap2470_checked : acceptsGraphIso
    (fused (graph core2470) (root 10) 0 0) DegreeOneSmallSpectrum1606.graph fusedMap2470=true := by decide +kernel
theorem certified2470 : Certified (graph core2470) (root 10) 0 0 :=
  of_native_maps core2470 DegreeOneSmallSpectrum2005.graph DegreeOneSmallSpectrum1606.graph
    sourceMap2470 fusedMap2470 sourceMap2470_checked fusedMap2470_checked
    DegreeOneSmallComparisons.comparison2470
#print axioms sourceMap2470_checked
#print axioms fusedMap2470_checked
#print axioms certified2470
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
