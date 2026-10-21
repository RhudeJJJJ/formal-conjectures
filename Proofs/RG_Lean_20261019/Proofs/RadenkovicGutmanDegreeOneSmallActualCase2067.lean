/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2067 : Family 10 := level10.get ⟨447,by decide⟩
def sourceMap2067 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2067 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2067_checked : acceptsGraphIso
    (source (graph core2067) (root 10) 0 0) DegreeOneSmallSpectrum1212.graph sourceMap2067=true := by decide +kernel
theorem fusedMap2067_checked : acceptsGraphIso
    (fused (graph core2067) (root 10) 0 0) DegreeOneSmallSpectrum1516.graph fusedMap2067=true := by decide +kernel
theorem certified2067 : Certified (graph core2067) (root 10) 0 0 :=
  of_native_maps core2067 DegreeOneSmallSpectrum1212.graph DegreeOneSmallSpectrum1516.graph
    sourceMap2067 fusedMap2067 sourceMap2067_checked fusedMap2067_checked
    DegreeOneSmallComparisons.comparison2067
#print axioms sourceMap2067_checked
#print axioms fusedMap2067_checked
#print axioms certified2067
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
