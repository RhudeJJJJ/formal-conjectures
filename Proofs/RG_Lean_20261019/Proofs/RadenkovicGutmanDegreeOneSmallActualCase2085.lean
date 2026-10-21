/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2085 : Family 10 := level10.get ⟨498,by decide⟩
def sourceMap2085 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2085 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2085_checked : acceptsGraphIso
    (source (graph core2085) (root 10) 0 0) DegreeOneSmallSpectrum1542.graph sourceMap2085=true := by decide +kernel
theorem fusedMap2085_checked : acceptsGraphIso
    (fused (graph core2085) (root 10) 0 0) DegreeOneSmallSpectrum980.graph fusedMap2085=true := by decide +kernel
theorem certified2085 : Certified (graph core2085) (root 10) 0 0 :=
  of_native_maps core2085 DegreeOneSmallSpectrum1542.graph DegreeOneSmallSpectrum980.graph
    sourceMap2085 fusedMap2085 sourceMap2085_checked fusedMap2085_checked
    DegreeOneSmallComparisons.comparison2085
#print axioms sourceMap2085_checked
#print axioms fusedMap2085_checked
#print axioms certified2085
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
