/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2213 : Family 10 := level10.get ⟨738,by decide⟩
def sourceMap2213 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2213 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2213_checked : acceptsGraphIso
    (source (graph core2213) (root 10) 0 0) DegreeOneSmallSpectrum1865.graph sourceMap2213=true := by decide +kernel
theorem fusedMap2213_checked : acceptsGraphIso
    (fused (graph core2213) (root 10) 0 0) DegreeOneSmallSpectrum1365.graph fusedMap2213=true := by decide +kernel
theorem certified2213 : Certified (graph core2213) (root 10) 0 0 :=
  of_native_maps core2213 DegreeOneSmallSpectrum1865.graph DegreeOneSmallSpectrum1365.graph
    sourceMap2213 fusedMap2213 sourceMap2213_checked fusedMap2213_checked
    DegreeOneSmallComparisons.comparison2213
#print axioms sourceMap2213_checked
#print axioms fusedMap2213_checked
#print axioms certified2213
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
