/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2025 : Family 10 := level10.get ⟨376,by decide⟩
def sourceMap2025 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2025 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2025_checked : acceptsGraphIso
    (source (graph core2025) (root 10) 0 0) DegreeOneSmallSpectrum1279.graph sourceMap2025=true := by decide +kernel
theorem fusedMap2025_checked : acceptsGraphIso
    (fused (graph core2025) (root 10) 0 0) DegreeOneSmallSpectrum1478.graph fusedMap2025=true := by decide +kernel
theorem certified2025 : Certified (graph core2025) (root 10) 0 0 :=
  of_native_maps core2025 DegreeOneSmallSpectrum1279.graph DegreeOneSmallSpectrum1478.graph
    sourceMap2025 fusedMap2025 sourceMap2025_checked fusedMap2025_checked
    DegreeOneSmallComparisons.comparison2025
#print axioms sourceMap2025_checked
#print axioms fusedMap2025_checked
#print axioms certified2025
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
