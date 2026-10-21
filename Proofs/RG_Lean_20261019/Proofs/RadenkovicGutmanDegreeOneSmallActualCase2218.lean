/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2218 : Family 10 := level10.get ⟨744,by decide⟩
def sourceMap2218 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2218 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2218_checked : acceptsGraphIso
    (source (graph core2218) (root 10) 0 0) DegreeOneSmallSpectrum1828.graph sourceMap2218=true := by decide +kernel
theorem fusedMap2218_checked : acceptsGraphIso
    (fused (graph core2218) (root 10) 0 0) DegreeOneSmallSpectrum1373.graph fusedMap2218=true := by decide +kernel
theorem certified2218 : Certified (graph core2218) (root 10) 0 0 :=
  of_native_maps core2218 DegreeOneSmallSpectrum1828.graph DegreeOneSmallSpectrum1373.graph
    sourceMap2218 fusedMap2218 sourceMap2218_checked fusedMap2218_checked
    DegreeOneSmallComparisons.comparison2218
#print axioms sourceMap2218_checked
#print axioms fusedMap2218_checked
#print axioms certified2218
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
