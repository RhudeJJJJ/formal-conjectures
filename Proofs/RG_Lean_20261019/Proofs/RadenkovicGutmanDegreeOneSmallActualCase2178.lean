/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2178 : Family 10 := level10.get ⟨659,by decide⟩
def sourceMap2178 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2178 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2178_checked : acceptsGraphIso
    (source (graph core2178) (root 10) 0 0) DegreeOneSmallSpectrum1707.graph sourceMap2178=true := by decide +kernel
theorem fusedMap2178_checked : acceptsGraphIso
    (fused (graph core2178) (root 10) 0 0) DegreeOneSmallSpectrum1277.graph fusedMap2178=true := by decide +kernel
theorem certified2178 : Certified (graph core2178) (root 10) 0 0 :=
  of_native_maps core2178 DegreeOneSmallSpectrum1707.graph DegreeOneSmallSpectrum1277.graph
    sourceMap2178 fusedMap2178 sourceMap2178_checked fusedMap2178_checked
    DegreeOneSmallComparisons.comparison2178
#print axioms sourceMap2178_checked
#print axioms fusedMap2178_checked
#print axioms certified2178
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
