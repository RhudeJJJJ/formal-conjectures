/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2201 : Family 10 := level10.get ⟨713,by decide⟩
def sourceMap2201 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,6,0,1,2,3,4,5,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2201 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2201_checked : acceptsGraphIso
    (source (graph core2201) (root 10) 0 0) DegreeOneSmallSpectrum1341.graph sourceMap2201=true := by decide +kernel
theorem fusedMap2201_checked : acceptsGraphIso
    (fused (graph core2201) (root 10) 0 0) DegreeOneSmallSpectrum1340.graph fusedMap2201=true := by decide +kernel
theorem certified2201 : Certified (graph core2201) (root 10) 0 0 :=
  of_native_maps core2201 DegreeOneSmallSpectrum1341.graph DegreeOneSmallSpectrum1340.graph
    sourceMap2201 fusedMap2201 sourceMap2201_checked fusedMap2201_checked
    DegreeOneSmallComparisons.comparison2201
#print axioms sourceMap2201_checked
#print axioms fusedMap2201_checked
#print axioms certified2201
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
