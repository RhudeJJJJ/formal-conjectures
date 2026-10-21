/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2307 : Family 10 := level10.get ⟨950,by decide⟩
def sourceMap2307 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,10,11,12,5,6,7,8,9,3,4] (sourceLabel 10 0 0 v)
def fusedMap2307 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,4,5,6,7,8,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2307_checked : acceptsGraphIso
    (source (graph core2307) (root 10) 0 0) DegreeOneSmallSpectrum1737.graph sourceMap2307=true := by decide +kernel
theorem fusedMap2307_checked : acceptsGraphIso
    (fused (graph core2307) (root 10) 0 0) DegreeOneSmallSpectrum1479.graph fusedMap2307=true := by decide +kernel
theorem certified2307 : Certified (graph core2307) (root 10) 0 0 :=
  of_native_maps core2307 DegreeOneSmallSpectrum1737.graph DegreeOneSmallSpectrum1479.graph
    sourceMap2307 fusedMap2307 sourceMap2307_checked fusedMap2307_checked
    DegreeOneSmallComparisons.comparison2307
#print axioms sourceMap2307_checked
#print axioms fusedMap2307_checked
#print axioms certified2307
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
