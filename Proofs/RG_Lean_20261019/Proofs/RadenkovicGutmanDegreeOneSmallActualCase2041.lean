/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2041 : Family 10 := level10.get ⟨399,by decide⟩
def sourceMap2041 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2041 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2041_checked : acceptsGraphIso
    (source (graph core2041) (root 10) 0 0) DegreeOneSmallSpectrum1133.graph sourceMap2041=true := by decide +kernel
theorem fusedMap2041_checked : acceptsGraphIso
    (fused (graph core2041) (root 10) 0 0) DegreeOneSmallSpectrum1498.graph fusedMap2041=true := by decide +kernel
theorem certified2041 : Certified (graph core2041) (root 10) 0 0 :=
  of_native_maps core2041 DegreeOneSmallSpectrum1133.graph DegreeOneSmallSpectrum1498.graph
    sourceMap2041 fusedMap2041 sourceMap2041_checked fusedMap2041_checked
    DegreeOneSmallComparisons.comparison2041
#print axioms sourceMap2041_checked
#print axioms fusedMap2041_checked
#print axioms certified2041
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
