/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2195 : Family 10 := level10.get ⟨702,by decide⟩
def sourceMap2195 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2195 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2195_checked : acceptsGraphIso
    (source (graph core2195) (root 10) 0 0) DegreeOneSmallSpectrum1858.graph sourceMap2195=true := by decide +kernel
theorem fusedMap2195_checked : acceptsGraphIso
    (fused (graph core2195) (root 10) 0 0) DegreeOneSmallSpectrum1316.graph fusedMap2195=true := by decide +kernel
theorem certified2195 : Certified (graph core2195) (root 10) 0 0 :=
  of_native_maps core2195 DegreeOneSmallSpectrum1858.graph DegreeOneSmallSpectrum1316.graph
    sourceMap2195 fusedMap2195 sourceMap2195_checked fusedMap2195_checked
    DegreeOneSmallComparisons.comparison2195
#print axioms sourceMap2195_checked
#print axioms fusedMap2195_checked
#print axioms certified2195
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
