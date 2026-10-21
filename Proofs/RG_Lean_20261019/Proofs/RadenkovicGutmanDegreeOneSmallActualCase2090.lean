/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2090 : Family 10 := level10.get ⟨504,by decide⟩
def sourceMap2090 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2090 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2090_checked : acceptsGraphIso
    (source (graph core2090) (root 10) 0 0) DegreeOneSmallSpectrum1581.graph sourceMap2090=true := by decide +kernel
theorem fusedMap2090_checked : acceptsGraphIso
    (fused (graph core2090) (root 10) 0 0) DegreeOneSmallSpectrum988.graph fusedMap2090=true := by decide +kernel
theorem certified2090 : Certified (graph core2090) (root 10) 0 0 :=
  of_native_maps core2090 DegreeOneSmallSpectrum1581.graph DegreeOneSmallSpectrum988.graph
    sourceMap2090 fusedMap2090 sourceMap2090_checked fusedMap2090_checked
    DegreeOneSmallComparisons.comparison2090
#print axioms sourceMap2090_checked
#print axioms fusedMap2090_checked
#print axioms certified2090
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
