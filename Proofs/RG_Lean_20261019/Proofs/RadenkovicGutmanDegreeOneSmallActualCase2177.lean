/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2177 : Family 10 := level10.get ⟨658,by decide⟩
def sourceMap2177 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,1,0,9,10,11,12,2,3,4,5,7,8] (sourceLabel 10 0 0 v)
def fusedMap2177 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2177_checked : acceptsGraphIso
    (source (graph core2177) (root 10) 0 0) DegreeOneSmallSpectrum1612.graph sourceMap2177=true := by decide +kernel
theorem fusedMap2177_checked : acceptsGraphIso
    (fused (graph core2177) (root 10) 0 0) DegreeOneSmallSpectrum1276.graph fusedMap2177=true := by decide +kernel
theorem certified2177 : Certified (graph core2177) (root 10) 0 0 :=
  of_native_maps core2177 DegreeOneSmallSpectrum1612.graph DegreeOneSmallSpectrum1276.graph
    sourceMap2177 fusedMap2177 sourceMap2177_checked fusedMap2177_checked
    DegreeOneSmallComparisons.comparison2177
#print axioms sourceMap2177_checked
#print axioms fusedMap2177_checked
#print axioms certified2177
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
