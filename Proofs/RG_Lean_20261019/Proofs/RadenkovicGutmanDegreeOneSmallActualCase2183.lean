/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2183 : Family 10 := level10.get ⟨684,by decide⟩
def sourceMap2183 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2183 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2183_checked : acceptsGraphIso
    (source (graph core2183) (root 10) 0 0) DegreeOneSmallSpectrum1850.graph sourceMap2183=true := by decide +kernel
theorem fusedMap2183_checked : acceptsGraphIso
    (fused (graph core2183) (root 10) 0 0) DegreeOneSmallSpectrum1293.graph fusedMap2183=true := by decide +kernel
theorem certified2183 : Certified (graph core2183) (root 10) 0 0 :=
  of_native_maps core2183 DegreeOneSmallSpectrum1850.graph DegreeOneSmallSpectrum1293.graph
    sourceMap2183 fusedMap2183 sourceMap2183_checked fusedMap2183_checked
    DegreeOneSmallComparisons.comparison2183
#print axioms sourceMap2183_checked
#print axioms fusedMap2183_checked
#print axioms certified2183
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
