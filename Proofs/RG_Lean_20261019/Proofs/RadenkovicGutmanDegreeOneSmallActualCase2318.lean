/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2318 : Family 10 := level10.get ⟨1009,by decide⟩
def sourceMap2318 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2318 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2318_checked : acceptsGraphIso
    (source (graph core2318) (root 10) 0 0) DegreeOneSmallSpectrum1561.graph sourceMap2318=true := by decide +kernel
theorem fusedMap2318_checked : acceptsGraphIso
    (fused (graph core2318) (root 10) 0 0) DegreeOneSmallSpectrum1563.graph fusedMap2318=true := by decide +kernel
theorem certified2318 : Certified (graph core2318) (root 10) 0 0 :=
  of_native_maps core2318 DegreeOneSmallSpectrum1561.graph DegreeOneSmallSpectrum1563.graph
    sourceMap2318 fusedMap2318 sourceMap2318_checked fusedMap2318_checked
    DegreeOneSmallComparisons.comparison2318
#print axioms sourceMap2318_checked
#print axioms fusedMap2318_checked
#print axioms certified2318
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
