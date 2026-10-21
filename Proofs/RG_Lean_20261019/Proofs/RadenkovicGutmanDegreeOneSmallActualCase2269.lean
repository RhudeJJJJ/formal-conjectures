/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2269 : Family 10 := level10.get ⟨856,by decide⟩
def sourceMap2269 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2269 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2269_checked : acceptsGraphIso
    (source (graph core2269) (root 10) 0 0) DegreeOneSmallSpectrum1837.graph sourceMap2269=true := by decide +kernel
theorem fusedMap2269_checked : acceptsGraphIso
    (fused (graph core2269) (root 10) 0 0) DegreeOneSmallSpectrum1480.graph fusedMap2269=true := by decide +kernel
theorem certified2269 : Certified (graph core2269) (root 10) 0 0 :=
  of_native_maps core2269 DegreeOneSmallSpectrum1837.graph DegreeOneSmallSpectrum1480.graph
    sourceMap2269 fusedMap2269 sourceMap2269_checked fusedMap2269_checked
    DegreeOneSmallComparisons.comparison2269
#print axioms sourceMap2269_checked
#print axioms fusedMap2269_checked
#print axioms certified2269
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
