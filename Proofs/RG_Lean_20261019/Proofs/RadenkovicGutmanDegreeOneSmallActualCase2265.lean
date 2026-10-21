/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2265 : Family 10 := level10.get ⟨848,by decide⟩
def sourceMap2265 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2265 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2265_checked : acceptsGraphIso
    (source (graph core2265) (root 10) 0 0) DegreeOneSmallSpectrum1808.graph sourceMap2265=true := by decide +kernel
theorem fusedMap2265_checked : acceptsGraphIso
    (fused (graph core2265) (root 10) 0 0) DegreeOneSmallSpectrum1473.graph fusedMap2265=true := by decide +kernel
theorem certified2265 : Certified (graph core2265) (root 10) 0 0 :=
  of_native_maps core2265 DegreeOneSmallSpectrum1808.graph DegreeOneSmallSpectrum1473.graph
    sourceMap2265 fusedMap2265 sourceMap2265_checked fusedMap2265_checked
    DegreeOneSmallComparisons.comparison2265
#print axioms sourceMap2265_checked
#print axioms fusedMap2265_checked
#print axioms certified2265
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
