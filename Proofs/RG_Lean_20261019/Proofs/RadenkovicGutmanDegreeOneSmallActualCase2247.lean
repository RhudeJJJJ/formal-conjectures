/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2247 : Family 10 := level10.get ⟨803,by decide⟩
def sourceMap2247 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,5,0,1,2,3,4,6,7,8,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2247 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2247_checked : acceptsGraphIso
    (source (graph core2247) (root 10) 0 0) DegreeOneSmallSpectrum1441.graph sourceMap2247=true := by decide +kernel
theorem fusedMap2247_checked : acceptsGraphIso
    (fused (graph core2247) (root 10) 0 0) DegreeOneSmallSpectrum1438.graph fusedMap2247=true := by decide +kernel
theorem certified2247 : Certified (graph core2247) (root 10) 0 0 :=
  of_native_maps core2247 DegreeOneSmallSpectrum1441.graph DegreeOneSmallSpectrum1438.graph
    sourceMap2247 fusedMap2247 sourceMap2247_checked fusedMap2247_checked
    DegreeOneSmallComparisons.comparison2247
#print axioms sourceMap2247_checked
#print axioms fusedMap2247_checked
#print axioms certified2247
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
