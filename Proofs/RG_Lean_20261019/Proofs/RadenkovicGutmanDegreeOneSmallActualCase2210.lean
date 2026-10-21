/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2210 : Family 10 := level10.get ⟨731,by decide⟩
def sourceMap2210 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2210 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2210_checked : acceptsGraphIso
    (source (graph core2210) (root 10) 0 0) DegreeOneSmallSpectrum1826.graph sourceMap2210=true := by decide +kernel
theorem fusedMap2210_checked : acceptsGraphIso
    (fused (graph core2210) (root 10) 0 0) DegreeOneSmallSpectrum1357.graph fusedMap2210=true := by decide +kernel
theorem certified2210 : Certified (graph core2210) (root 10) 0 0 :=
  of_native_maps core2210 DegreeOneSmallSpectrum1826.graph DegreeOneSmallSpectrum1357.graph
    sourceMap2210 fusedMap2210 sourceMap2210_checked fusedMap2210_checked
    DegreeOneSmallComparisons.comparison2210
#print axioms sourceMap2210_checked
#print axioms fusedMap2210_checked
#print axioms certified2210
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
