/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2237 : Family 10 := level10.get ⟨781,by decide⟩
def sourceMap2237 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2237 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2237_checked : acceptsGraphIso
    (source (graph core2237) (root 10) 0 0) DegreeOneSmallSpectrum1832.graph sourceMap2237=true := by decide +kernel
theorem fusedMap2237_checked : acceptsGraphIso
    (fused (graph core2237) (root 10) 0 0) DegreeOneSmallSpectrum1417.graph fusedMap2237=true := by decide +kernel
theorem certified2237 : Certified (graph core2237) (root 10) 0 0 :=
  of_native_maps core2237 DegreeOneSmallSpectrum1832.graph DegreeOneSmallSpectrum1417.graph
    sourceMap2237 fusedMap2237 sourceMap2237_checked fusedMap2237_checked
    DegreeOneSmallComparisons.comparison2237
#print axioms sourceMap2237_checked
#print axioms fusedMap2237_checked
#print axioms certified2237
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
