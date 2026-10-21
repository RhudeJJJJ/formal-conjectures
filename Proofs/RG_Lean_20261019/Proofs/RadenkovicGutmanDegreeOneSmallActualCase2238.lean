/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2238 : Family 10 := level10.get ⟨783,by decide⟩
def sourceMap2238 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2238 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2238_checked : acceptsGraphIso
    (source (graph core2238) (root 10) 0 0) DegreeOneSmallSpectrum1769.graph sourceMap2238=true := by decide +kernel
theorem fusedMap2238_checked : acceptsGraphIso
    (fused (graph core2238) (root 10) 0 0) DegreeOneSmallSpectrum1421.graph fusedMap2238=true := by decide +kernel
theorem certified2238 : Certified (graph core2238) (root 10) 0 0 :=
  of_native_maps core2238 DegreeOneSmallSpectrum1769.graph DegreeOneSmallSpectrum1421.graph
    sourceMap2238 fusedMap2238 sourceMap2238_checked fusedMap2238_checked
    DegreeOneSmallComparisons.comparison2238
#print axioms sourceMap2238_checked
#print axioms fusedMap2238_checked
#print axioms certified2238
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
