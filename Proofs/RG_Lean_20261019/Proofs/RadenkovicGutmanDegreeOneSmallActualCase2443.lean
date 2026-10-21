/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2443 : Family 10 := level10.get ⟨1407,by decide⟩
def sourceMap2443 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2443 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2443_checked : acceptsGraphIso
    (source (graph core2443) (root 10) 0 0) DegreeOneSmallSpectrum1981.graph sourceMap2443=true := by decide +kernel
theorem fusedMap2443_checked : acceptsGraphIso
    (fused (graph core2443) (root 10) 0 0) DegreeOneSmallSpectrum1974.graph fusedMap2443=true := by decide +kernel
theorem certified2443 : Certified (graph core2443) (root 10) 0 0 :=
  of_native_maps core2443 DegreeOneSmallSpectrum1981.graph DegreeOneSmallSpectrum1974.graph
    sourceMap2443 fusedMap2443 sourceMap2443_checked fusedMap2443_checked
    DegreeOneSmallComparisons.comparison2443
#print axioms sourceMap2443_checked
#print axioms fusedMap2443_checked
#print axioms certified2443
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
