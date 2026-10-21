/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2266 : Family 10 := level10.get ⟨852,by decide⟩
def sourceMap2266 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2266 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2266_checked : acceptsGraphIso
    (source (graph core2266) (root 10) 0 0) DegreeOneSmallSpectrum1882.graph sourceMap2266=true := by decide +kernel
theorem fusedMap2266_checked : acceptsGraphIso
    (fused (graph core2266) (root 10) 0 0) DegreeOneSmallSpectrum1476.graph fusedMap2266=true := by decide +kernel
theorem certified2266 : Certified (graph core2266) (root 10) 0 0 :=
  of_native_maps core2266 DegreeOneSmallSpectrum1882.graph DegreeOneSmallSpectrum1476.graph
    sourceMap2266 fusedMap2266 sourceMap2266_checked fusedMap2266_checked
    DegreeOneSmallComparisons.comparison2266
#print axioms sourceMap2266_checked
#print axioms fusedMap2266_checked
#print axioms certified2266
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
