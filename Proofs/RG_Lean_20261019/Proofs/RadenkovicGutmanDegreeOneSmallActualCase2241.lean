/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2241 : Family 10 := level10.get ⟨789,by decide⟩
def sourceMap2241 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2241 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2241_checked : acceptsGraphIso
    (source (graph core2241) (root 10) 0 0) DegreeOneSmallSpectrum1720.graph sourceMap2241=true := by decide +kernel
theorem fusedMap2241_checked : acceptsGraphIso
    (fused (graph core2241) (root 10) 0 0) DegreeOneSmallSpectrum1428.graph fusedMap2241=true := by decide +kernel
theorem certified2241 : Certified (graph core2241) (root 10) 0 0 :=
  of_native_maps core2241 DegreeOneSmallSpectrum1720.graph DegreeOneSmallSpectrum1428.graph
    sourceMap2241 fusedMap2241 sourceMap2241_checked fusedMap2241_checked
    DegreeOneSmallComparisons.comparison2241
#print axioms sourceMap2241_checked
#print axioms fusedMap2241_checked
#print axioms certified2241
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
