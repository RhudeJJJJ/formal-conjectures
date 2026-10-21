/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2286 : Family 10 := level10.get ⟨897,by decide⟩
def sourceMap2286 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,8,9,10,11,12,1,2,3,4,6,7] (sourceLabel 10 0 0 v)
def fusedMap2286 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,8,9,10,11,12,1,2,3,4,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2286_checked : acceptsGraphIso
    (source (graph core2286) (root 10) 0 0) DegreeOneSmallSpectrum1402.graph sourceMap2286=true := by decide +kernel
theorem fusedMap2286_checked : acceptsGraphIso
    (fused (graph core2286) (root 10) 0 0) DegreeOneSmallSpectrum1397.graph fusedMap2286=true := by decide +kernel
theorem certified2286 : Certified (graph core2286) (root 10) 0 0 :=
  of_native_maps core2286 DegreeOneSmallSpectrum1402.graph DegreeOneSmallSpectrum1397.graph
    sourceMap2286 fusedMap2286 sourceMap2286_checked fusedMap2286_checked
    DegreeOneSmallComparisons.comparison2286
#print axioms sourceMap2286_checked
#print axioms fusedMap2286_checked
#print axioms certified2286
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
