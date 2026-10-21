/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2158 : Family 10 := level10.get ⟨621,by decide⟩
def sourceMap2158 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2158 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2158_checked : acceptsGraphIso
    (source (graph core2158) (root 10) 0 0) DegreeOneSmallSpectrum1843.graph sourceMap2158=true := by decide +kernel
theorem fusedMap2158_checked : acceptsGraphIso
    (fused (graph core2158) (root 10) 0 0) DegreeOneSmallSpectrum1191.graph fusedMap2158=true := by decide +kernel
theorem certified2158 : Certified (graph core2158) (root 10) 0 0 :=
  of_native_maps core2158 DegreeOneSmallSpectrum1843.graph DegreeOneSmallSpectrum1191.graph
    sourceMap2158 fusedMap2158 sourceMap2158_checked fusedMap2158_checked
    DegreeOneSmallComparisons.comparison2158
#print axioms sourceMap2158_checked
#print axioms fusedMap2158_checked
#print axioms certified2158
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
