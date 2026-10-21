/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2109 : Family 10 := level10.get ⟨534,by decide⟩
def sourceMap2109 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2109 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2109_checked : acceptsGraphIso
    (source (graph core2109) (root 10) 0 0) DegreeOneSmallSpectrum1681.graph sourceMap2109=true := by decide +kernel
theorem fusedMap2109_checked : acceptsGraphIso
    (fused (graph core2109) (root 10) 0 0) DegreeOneSmallSpectrum1038.graph fusedMap2109=true := by decide +kernel
theorem certified2109 : Certified (graph core2109) (root 10) 0 0 :=
  of_native_maps core2109 DegreeOneSmallSpectrum1681.graph DegreeOneSmallSpectrum1038.graph
    sourceMap2109 fusedMap2109 sourceMap2109_checked fusedMap2109_checked
    DegreeOneSmallComparisons.comparison2109
#print axioms sourceMap2109_checked
#print axioms fusedMap2109_checked
#print axioms certified2109
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
