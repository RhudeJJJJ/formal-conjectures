/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2077 : Family 10 := level10.get ⟨469,by decide⟩
def sourceMap2077 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,1,0,9,10,11,12,2,3,4,5,7,8] (sourceLabel 10 0 0 v)
def fusedMap2077 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,1,0,9,10,11,12,2,3,4,5,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2077_checked : acceptsGraphIso
    (source (graph core2077) (root 10) 0 0) DegreeOneSmallSpectrum1403.graph sourceMap2077=true := by decide +kernel
theorem fusedMap2077_checked : acceptsGraphIso
    (fused (graph core2077) (root 10) 0 0) DegreeOneSmallSpectrum1398.graph fusedMap2077=true := by decide +kernel
theorem certified2077 : Certified (graph core2077) (root 10) 0 0 :=
  of_native_maps core2077 DegreeOneSmallSpectrum1403.graph DegreeOneSmallSpectrum1398.graph
    sourceMap2077 fusedMap2077 sourceMap2077_checked fusedMap2077_checked
    DegreeOneSmallComparisons.comparison2077
#print axioms sourceMap2077_checked
#print axioms fusedMap2077_checked
#print axioms certified2077
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
