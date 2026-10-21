/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2236 : Family 10 := level10.get ⟨780,by decide⟩
def sourceMap2236 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2236 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2236_checked : acceptsGraphIso
    (source (graph core2236) (root 10) 0 0) DegreeOneSmallSpectrum1875.graph sourceMap2236=true := by decide +kernel
theorem fusedMap2236_checked : acceptsGraphIso
    (fused (graph core2236) (root 10) 0 0) DegreeOneSmallSpectrum1415.graph fusedMap2236=true := by decide +kernel
theorem certified2236 : Certified (graph core2236) (root 10) 0 0 :=
  of_native_maps core2236 DegreeOneSmallSpectrum1875.graph DegreeOneSmallSpectrum1415.graph
    sourceMap2236 fusedMap2236 sourceMap2236_checked fusedMap2236_checked
    DegreeOneSmallComparisons.comparison2236
#print axioms sourceMap2236_checked
#print axioms fusedMap2236_checked
#print axioms certified2236
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
