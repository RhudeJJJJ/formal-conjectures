/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2288 : Family 10 := level10.get ⟨900,by decide⟩
def sourceMap2288 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,1,0,9,10,11,12,2,3,4,5,7,8] (sourceLabel 10 0 0 v)
def fusedMap2288 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,4,5,6,7,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2288_checked : acceptsGraphIso
    (source (graph core2288) (root 10) 0 0) DegreeOneSmallSpectrum1616.graph sourceMap2288=true := by decide +kernel
theorem fusedMap2288_checked : acceptsGraphIso
    (fused (graph core2288) (root 10) 0 0) DegreeOneSmallSpectrum1466.graph fusedMap2288=true := by decide +kernel
theorem certified2288 : Certified (graph core2288) (root 10) 0 0 :=
  of_native_maps core2288 DegreeOneSmallSpectrum1616.graph DegreeOneSmallSpectrum1466.graph
    sourceMap2288 fusedMap2288 sourceMap2288_checked fusedMap2288_checked
    DegreeOneSmallComparisons.comparison2288
#print axioms sourceMap2288_checked
#print axioms fusedMap2288_checked
#print axioms certified2288
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
