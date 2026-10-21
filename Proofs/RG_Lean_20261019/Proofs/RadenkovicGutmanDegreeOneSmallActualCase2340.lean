/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2340 : Family 10 := level10.get ⟨1053,by decide⟩
def sourceMap2340 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2340 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2340_checked : acceptsGraphIso
    (source (graph core2340) (root 10) 0 0) DegreeOneSmallSpectrum1667.graph sourceMap2340=true := by decide +kernel
theorem fusedMap2340_checked : acceptsGraphIso
    (fused (graph core2340) (root 10) 0 0) DegreeOneSmallSpectrum1666.graph fusedMap2340=true := by decide +kernel
theorem certified2340 : Certified (graph core2340) (root 10) 0 0 :=
  of_native_maps core2340 DegreeOneSmallSpectrum1667.graph DegreeOneSmallSpectrum1666.graph
    sourceMap2340 fusedMap2340 sourceMap2340_checked fusedMap2340_checked
    DegreeOneSmallComparisons.comparison2340
#print axioms sourceMap2340_checked
#print axioms fusedMap2340_checked
#print axioms certified2340
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
