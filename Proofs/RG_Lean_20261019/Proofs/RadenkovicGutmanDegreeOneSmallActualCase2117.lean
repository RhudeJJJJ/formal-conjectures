/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2117 : Family 10 := level10.get ⟨547,by decide⟩
def sourceMap2117 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,6,0,1,2,3,4,5,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2117 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2117_checked : acceptsGraphIso
    (source (graph core2117) (root 10) 0 0) DegreeOneSmallSpectrum1075.graph sourceMap2117=true := by decide +kernel
theorem fusedMap2117_checked : acceptsGraphIso
    (fused (graph core2117) (root 10) 0 0) DegreeOneSmallSpectrum1074.graph fusedMap2117=true := by decide +kernel
theorem certified2117 : Certified (graph core2117) (root 10) 0 0 :=
  of_native_maps core2117 DegreeOneSmallSpectrum1075.graph DegreeOneSmallSpectrum1074.graph
    sourceMap2117 fusedMap2117 sourceMap2117_checked fusedMap2117_checked
    DegreeOneSmallComparisons.comparison2117
#print axioms sourceMap2117_checked
#print axioms fusedMap2117_checked
#print axioms certified2117
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
