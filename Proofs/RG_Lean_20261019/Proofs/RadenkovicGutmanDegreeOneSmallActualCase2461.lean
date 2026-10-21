/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2461 : Family 10 := level10.get ⟨1532,by decide⟩
def sourceMap2461 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2461 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2461_checked : acceptsGraphIso
    (source (graph core2461) (root 10) 0 0) DegreeOneSmallSpectrum1996.graph sourceMap2461=true := by decide +kernel
theorem fusedMap2461_checked : acceptsGraphIso
    (fused (graph core2461) (root 10) 0 0) DegreeOneSmallSpectrum1533.graph fusedMap2461=true := by decide +kernel
theorem certified2461 : Certified (graph core2461) (root 10) 0 0 :=
  of_native_maps core2461 DegreeOneSmallSpectrum1996.graph DegreeOneSmallSpectrum1533.graph
    sourceMap2461 fusedMap2461 sourceMap2461_checked fusedMap2461_checked
    DegreeOneSmallComparisons.comparison2461
#print axioms sourceMap2461_checked
#print axioms fusedMap2461_checked
#print axioms certified2461
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
