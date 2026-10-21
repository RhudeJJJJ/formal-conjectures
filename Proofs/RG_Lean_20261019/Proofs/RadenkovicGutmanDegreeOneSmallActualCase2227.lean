/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2227 : Family 10 := level10.get ⟨765,by decide⟩
def sourceMap2227 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2227 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2227_checked : acceptsGraphIso
    (source (graph core2227) (root 10) 0 0) DegreeOneSmallSpectrum1829.graph sourceMap2227=true := by decide +kernel
theorem fusedMap2227_checked : acceptsGraphIso
    (fused (graph core2227) (root 10) 0 0) DegreeOneSmallSpectrum1397.graph fusedMap2227=true := by decide +kernel
theorem certified2227 : Certified (graph core2227) (root 10) 0 0 :=
  of_native_maps core2227 DegreeOneSmallSpectrum1829.graph DegreeOneSmallSpectrum1397.graph
    sourceMap2227 fusedMap2227 sourceMap2227_checked fusedMap2227_checked
    DegreeOneSmallComparisons.comparison2227
#print axioms sourceMap2227_checked
#print axioms fusedMap2227_checked
#print axioms certified2227
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
