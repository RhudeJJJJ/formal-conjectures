/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2343 : Family 10 := level10.get ⟨1057,by decide⟩
def sourceMap2343 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2343 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2343_checked : acceptsGraphIso
    (source (graph core2343) (root 10) 0 0) DegreeOneSmallSpectrum1658.graph sourceMap2343=true := by decide +kernel
theorem fusedMap2343_checked : acceptsGraphIso
    (fused (graph core2343) (root 10) 0 0) DegreeOneSmallSpectrum1669.graph fusedMap2343=true := by decide +kernel
theorem certified2343 : Certified (graph core2343) (root 10) 0 0 :=
  of_native_maps core2343 DegreeOneSmallSpectrum1658.graph DegreeOneSmallSpectrum1669.graph
    sourceMap2343 fusedMap2343 sourceMap2343_checked fusedMap2343_checked
    DegreeOneSmallComparisons.comparison2343
#print axioms sourceMap2343_checked
#print axioms fusedMap2343_checked
#print axioms certified2343
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
