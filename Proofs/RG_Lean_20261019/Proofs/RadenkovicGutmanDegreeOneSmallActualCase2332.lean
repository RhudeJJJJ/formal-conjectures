/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2332 : Family 10 := level10.get ⟨1037,by decide⟩
def sourceMap2332 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2332 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2332_checked : acceptsGraphIso
    (source (graph core2332) (root 10) 0 0) DegreeOneSmallSpectrum1622.graph sourceMap2332=true := by decide +kernel
theorem fusedMap2332_checked : acceptsGraphIso
    (fused (graph core2332) (root 10) 0 0) DegreeOneSmallSpectrum1624.graph fusedMap2332=true := by decide +kernel
theorem certified2332 : Certified (graph core2332) (root 10) 0 0 :=
  of_native_maps core2332 DegreeOneSmallSpectrum1622.graph DegreeOneSmallSpectrum1624.graph
    sourceMap2332 fusedMap2332 sourceMap2332_checked fusedMap2332_checked
    DegreeOneSmallComparisons.comparison2332
#print axioms sourceMap2332_checked
#print axioms fusedMap2332_checked
#print axioms certified2332
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
