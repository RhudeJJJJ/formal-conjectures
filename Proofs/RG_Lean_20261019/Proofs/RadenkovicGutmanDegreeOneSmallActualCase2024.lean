/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2024 : Family 10 := level10.get ⟨374,by decide⟩
def sourceMap2024 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2024 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2024_checked : acceptsGraphIso
    (source (graph core2024) (root 10) 0 0) DegreeOneSmallSpectrum1175.graph sourceMap2024=true := by decide +kernel
theorem fusedMap2024_checked : acceptsGraphIso
    (fused (graph core2024) (root 10) 0 0) DegreeOneSmallSpectrum1474.graph fusedMap2024=true := by decide +kernel
theorem certified2024 : Certified (graph core2024) (root 10) 0 0 :=
  of_native_maps core2024 DegreeOneSmallSpectrum1175.graph DegreeOneSmallSpectrum1474.graph
    sourceMap2024 fusedMap2024 sourceMap2024_checked fusedMap2024_checked
    DegreeOneSmallComparisons.comparison2024
#print axioms sourceMap2024_checked
#print axioms fusedMap2024_checked
#print axioms certified2024
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
