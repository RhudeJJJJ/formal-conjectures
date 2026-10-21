/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2079 : Family 10 := level10.get ⟨472,by decide⟩
def sourceMap2079 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,1,0,9,10,11,12,2,3,4,5,7,8] (sourceLabel 10 0 0 v)
def fusedMap2079 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2079_checked : acceptsGraphIso
    (source (graph core2079) (root 10) 0 0) DegreeOneSmallSpectrum1009.graph sourceMap2079=true := by decide +kernel
theorem fusedMap2079_checked : acceptsGraphIso
    (fused (graph core2079) (root 10) 0 0) DegreeOneSmallSpectrum1467.graph fusedMap2079=true := by decide +kernel
theorem certified2079 : Certified (graph core2079) (root 10) 0 0 :=
  of_native_maps core2079 DegreeOneSmallSpectrum1009.graph DegreeOneSmallSpectrum1467.graph
    sourceMap2079 fusedMap2079 sourceMap2079_checked fusedMap2079_checked
    DegreeOneSmallComparisons.comparison2079
#print axioms sourceMap2079_checked
#print axioms fusedMap2079_checked
#print axioms certified2079
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
