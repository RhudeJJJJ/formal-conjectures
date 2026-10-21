/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2108 : Family 10 := level10.get ⟨530,by decide⟩
def sourceMap2108 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2108 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2108_checked : acceptsGraphIso
    (source (graph core2108) (root 10) 0 0) DegreeOneSmallSpectrum1659.graph sourceMap2108=true := by decide +kernel
theorem fusedMap2108_checked : acceptsGraphIso
    (fused (graph core2108) (root 10) 0 0) DegreeOneSmallSpectrum1035.graph fusedMap2108=true := by decide +kernel
theorem certified2108 : Certified (graph core2108) (root 10) 0 0 :=
  of_native_maps core2108 DegreeOneSmallSpectrum1659.graph DegreeOneSmallSpectrum1035.graph
    sourceMap2108 fusedMap2108 sourceMap2108_checked fusedMap2108_checked
    DegreeOneSmallComparisons.comparison2108
#print axioms sourceMap2108_checked
#print axioms fusedMap2108_checked
#print axioms certified2108
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
